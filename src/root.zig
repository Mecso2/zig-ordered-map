const std = @import("std");
const AllocError: type = std.mem.Allocator.Error;

/// Given a struct pointer, and an offset, it returns a pointer to the field at that, offset
inline fn atOffset(stru: anytype, offset: usize, comptime T: type) *T {
    const info = @typeInfo(@TypeOf(stru));
    if (info != .Pointer or @typeInfo(info.Pointer.child) != .Struct) @compileError("Struct pointers only");
    return @ptrFromInt(@intFromPtr(stru) + offset);
}

/// Given a function type, it returns the return type of the function
fn returnType(comptime fun: type) ?type {
    return switch (@typeInfo(fun)) {
        .Fn => |f| f.return_type,
        else => @compileError("only for functions"),
    };
}

/// Given a function it returns the types of arguments it takes
///
/// - `argTypes(fn(u32, u8) void)` => `&[_]const ?type{u32, u8}`
/// - `argTypes(fn(u32, u8) noreturn)` => `&[_]const ?type{u32, u8}`
/// - `argTypes(fn([]u8, anytype) c_int)` => `&[_]const ?type{[]u8, null}`
fn argTypes(comptime Function: type) []const ?type {
    const info = @typeInfo(Function);
    if (info != .Fn)
        @compileError("argTypes expects a function type");

    const function_info = info.Fn;
    if (function_info.is_var_args)
        @compileError("Cannot use argTypes on variadic function");

    var argument_field_list: [function_info.params.len]?type = undefined;
    inline for (function_info.params, 0..) |arg, i| {
        const T = arg.type;
        argument_field_list[i] = T;
    }

    return argument_field_list[0..];
}

pub fn OrderedMap(comptime K: type, comptime V: type, ctx: anytype, comptime comp_fn: anytype) type {
    const inf = @typeInfo(@TypeOf(comp_fn));
    if (inf != .Fn) @compileError("comperison function must be a function");
    if (inf.Fn.return_type != std.math.Order) @compileError("retrun type of comperison function must be std.math.Order");
    const args = argTypes(@TypeOf(comp_fn));
    if (@TypeOf(ctx) == void and args.len != 2)
        @compileError("Contextless comperison function must take 2 arguments");
    if (@TypeOf(ctx) != void and (args.len != 3 or args[2] != @TypeOf(ctx)))
        @compileError("Contexty comperison function must take 3 arguments, of which the 3rd one is the context");
    if ((args[0] != null and args[0] != K) or
        (args[1] != null and args[1] != K))
        @compileError("Comperison function must take two key types(or anytypes) as its first two parameters");

    return struct {
        pub const Node: type = struct {
            parent: ?*@This() = null,
            left: ?*@This() = null,
            right: ?*@This() = null,
            color: enum { Red, Black } = .Red,

            key: K,
            value: V,

            const leftOffset: usize = @offsetOf(@This(), "left");
            const rightOffset: usize = @offsetOf(@This(), "right");
            pub fn jsonStringify(self: *const @This(), writeStream: anytype) !void {
                return writeStream.write(.{ .key = self.key, .value = self.value, .color = self.color, .left = self.left, .right = self.right });
            }

            /// Returns a pointer to the in-order next node
            pub fn next(self: *@This()) ?*@This() {
                if (self.right) |r| {
                    var node: *@This() = r;
                    while (node.left) |l| node = l;
                    return node;
                } else {
                    var node: *@This() = self;
                    return while (node.parent) |p| {
                        if (p.left == node) break p;
                        node = p;
                    } else null;
                }
            }
            /// Returns a pointer to the in-order previous node
            pub fn prev(self: *@This()) ?*@This() {
                if (self.left) |l| {
                    var node: *@This() = l;
                    while (node.right) |r| node = r;
                    return node;
                } else {
                    var node: *@This() = self;
                    return while (node.parent) |p| {
                        if (p.right == node) break p;
                        node = p;
                    } else null;
                }
            }
            fn balanceInsert(self: *@This()) void {
                var n: *@This() = self;
                while (n.parent != null and n.parent.?.color == .Red) {
                    var parent: *@This() = n.parent.?;
                    var grandparent: *@This() = parent.parent.?;
                    std.debug.assert(grandparent.color == .Black);

                    const uncle: ?*@This() = if (grandparent.right == parent) grandparent.left else grandparent.right;

                    //case 1:
                    if (uncle != null and uncle.?.color == .Red) {
                        parent.color = .Black;
                        uncle.?.color = .Black;
                        grandparent.color = .Red;
                        n = grandparent;
                        continue;
                    }

                    var side: usize = undefined;
                    var other_side: usize = undefined;
                    if (atOffset(parent, leftOffset, ?*@This()).* == n) {
                        side = leftOffset;
                        other_side = rightOffset;
                    } else {
                        std.debug.assert(atOffset(parent, rightOffset, ?*@This()).* == n);
                        side = rightOffset;
                        other_side = leftOffset;
                    }

                    //case 2:
                    if (atOffset(grandparent, other_side, ?*@This()).* == parent) {
                        //update children
                        atOffset(parent, side, ?*@This()).* = atOffset(n, other_side, ?*@This()).*;
                        atOffset(grandparent, other_side, ?*@This()).* = n;
                        atOffset(n, other_side, ?*@This()).* = parent;

                        //update parents
                        if (atOffset(parent, side, ?*@This()).*) |q| q.parent = parent;
                        n.parent = grandparent;
                        parent.parent = n;

                        n = parent;
                        parent = n.parent.?;

                        //switch sides for case 3
                        const tmp = side;
                        side = other_side;
                        other_side = tmp;
                    }

                    //case 3:
                    atOffset(grandparent, side, ?*@This()).* = atOffset(parent, other_side, ?*@This()).*;
                    if (grandparent.parent) |greatgrandparent|
                        (if (greatgrandparent.left == grandparent)
                            greatgrandparent.left
                        else
                            greatgrandparent.right) = parent;
                    atOffset(parent, other_side, ?*@This()).* = grandparent;

                    if (atOffset(grandparent, side, ?*@This()).*) |q| q.parent = grandparent;
                    parent.parent = grandparent.parent;
                    grandparent.parent = parent;

                    grandparent.color = .Red;
                    parent.color = .Black;

                    return;
                }

                if (n.parent == null) {
                    n.color = .Black;
                }
            }

            //Node with one null node(which is double Black), and a tree with one Black height
            fn balanceDelete(self: *@This()) void {
                var parent: ?*@This() = self;
                var double_Black: ?*@This() = null;
                while (parent) |n| {
                    var side: usize = undefined;
                    var other_side: usize = undefined;
                    if (atOffset(n, leftOffset, ?*@This()).* == double_Black) {
                        side = leftOffset;
                        other_side = rightOffset;
                    } else {
                        std.debug.assert(atOffset(n, rightOffset, ?*@This()).* == double_Black);
                        side = rightOffset;
                        other_side = leftOffset;
                    }

                    //there is a Black on this side there must me at least one on the other as well, so we have a sibling
                    const sibling: *@This() = atOffset(n, other_side, ?*@This()).*.?;

                    if (sibling.color == .Black) {
                        //has a Red nephew on the same side: sibling=n.right, n.right.right==Red
                        if (atOffset(sibling, other_side, ?*@This()).* != null and
                            atOffset(sibling, other_side, ?*@This()).*.?.color == .Red)
                        {
                            atOffset(n, other_side, ?*@This()).* = atOffset(sibling, side, ?*@This()).*;
                            if (n.parent) |p| {
                                (if (p.left == n) p.left else p.right) = sibling;
                            }
                            atOffset(sibling, side, ?*@This()).* = n;

                            if (atOffset(n, other_side, ?*@This()).*) |q| q.parent = n;
                            sibling.parent = n.parent;
                            n.parent = sibling;

                            atOffset(sibling, other_side, ?*@This()).*.?.color = .Black;
                            if (n.color == .Red) { //IDFK
                                n.color = .Black;
                                sibling.color = .Red;
                            }
                            return;
                        }

                        //has Red nephew on the other side as the sibling, same side as the db
                        if (atOffset(sibling, side, ?*@This()).* != null and
                            atOffset(sibling, side, ?*@This()).*.?.color == .Red)
                        {
                            const nephew = atOffset(sibling, side, ?*@This()).*.?;

                            atOffset(sibling, side, ?*@This()).* = atOffset(nephew, other_side, ?*@This()).*;
                            atOffset(n, other_side, ?*@This()).* = atOffset(nephew, side, ?*@This()).*;
                            if (n.parent) |p| {
                                (if (p.left == n) p.left else p.right) = nephew;
                            }
                            atOffset(nephew, side, ?*@This()).* = n;
                            atOffset(nephew, other_side, ?*@This()).* = sibling;

                            if (atOffset(sibling, side, ?*@This()).*) |q| q.parent = sibling;
                            if (atOffset(n, other_side, ?*@This()).*) |q| q.parent = n;
                            nephew.parent = n.parent;
                            n.parent = nephew;
                            sibling.parent = nephew;

                            if (n.color == .Red) sibling.color = .Red; //IDFK
                            nephew.color = .Black;
                            return;
                        }

                        //move up
                        sibling.color = .Red;
                        if (n.color == .Red) {
                            n.color = .Black;
                            return;
                        }
                        parent = n.parent;
                        double_Black = n;

                        continue;
                    }

                    atOffset(n, other_side, ?*@This()).* = atOffset(sibling, side, ?*@This()).*;
                    if (n.parent) |p| {
                        (if (p.left == n) p.left else p.right) = sibling;
                    }
                    atOffset(sibling, side, ?*Node).* = n;

                    if (atOffset(n, other_side, ?*@This()).*) |q| q.parent = n;
                    sibling.parent = n.parent;
                    n.parent = sibling;

                    sibling.color = .Black;
                    n.color = .Red;
                }
            }

            fn delete(self: *@This(), alloc: std.mem.Allocator) ?*@This() {
                const color = self.color;
                const parent = self.parent;

                if (self.left == null and self.right == null) {
                    alloc.destroy(self);
                    if (parent) |p| {
                        (if (p.left == self) p.left else p.right) = null;
                        if (color == .Black) balanceDelete(p);
                    }
                    return null;
                }
                if (self.left == null or self.right == null) {
                    const child = if (self.left) |l| l else self.right.?;
                    //the Black height of the left is 0 so must be the one of right ergo: child was Red
                    //Red can't be the parent of Red, so we must be right
                    std.debug.assert(child.color == .Red);
                    std.debug.assert(color == .Black);

                    //replace our selves with the child, the Red child gets coloRed Black to keep the balck height
                    child.parent = parent;
                    if (parent) |p| (if (p.left == self) p.left else p.right) = child;

                    alloc.destroy(self);
                    child.color = .Black;
                    return child;
                }
                const next_e = self.next().?;
                self.key = next_e.key;
                self.value = next_e.value;
                _ = next_e.delete(alloc);
                return self;
            }
        };
        const Iterator = struct {
            p: ?*Node,
            pub fn next(self: *@This()) ?*Node {
                const r = self.p;
                if (r) |t| self.p = t.next();

                return r;
            }
        };

        alloc: std.mem.Allocator,
        root: ?*Node = null,
        count: usize = 0,

        /// Deallocates the tree.
        /// This does *not* deinit keys or values!
        /// If your keys or values need to be released, ensure
        /// that that is done before calling this function.
        pub fn deinit(self: *@This()) void {
            if (self.root == null) return;
            var node: *Node = self.root.?;
            while (true) {
                if (node.left) |l| {
                    std.debug.assert(l.parent == node);
                    node.left = null;
                    node = l;
                    continue;
                }
                if (node.right) |r| {
                    std.debug.assert(r.parent == node);
                    node.right = null;
                    node = r;
                    continue;
                }

                const p: *Node = node.parent orelse {
                    std.debug.assert(node == self.root);
                    self.alloc.destroy(node);
                    break;
                };
                self.alloc.destroy(node);
                node = p;
            }

            self.count = 0;
            self.root = null;
        }

        /// Finds the value associated with a key in the map
        pub fn get(self: *const @This(), k: K) ?V {
            return if (self.getNode(k)) |n| n.value else null;
        }

        pub fn getNode(self: *const @This(), k: K) ?*Node {
            var n: *Node = self.root orelse return null;
            while (true) {
                switch (if (@TypeOf(ctx) == void) comp_fn(k, n.key) else comp_fn(k, n.key, ctx)) {
                    .eq => return n,
                    .lt => n = n.left orelse return null,
                    .gt => n = n.right orelse return null,
                }
            }
        }

        pub fn getFirstNode(self: *@This()) ?*Node {
            var node: *Node = self.root orelse return null;
            while (node.left) |l| node = l;
            return node;
        }

        pub fn deque(self: *@This()) ?V {
            return (self.dequeWithKey() orelse return null)[1];
        }
        pub fn dequeWithKey(self: *@This()) ?struct { K, V } {
            const node: *Node = self.getFirstNode() orelse return null;
            const r: returnType(@TypeOf(dequeWithKey)).? = .{ node.key, node.value };
            self.removeNode(node);

            return r;
        }

        pub fn getLastNode(self: *@This()) ?*Node {
            var r: *Node = self.root orelse return null;
            while (r.right) |c| r = c;
            return r;
        }

        /// Check if the map contains a key
        pub fn contains(self: *const @This(), k: K) bool {
            return self.getNode(k) != null;
        }

        pub const GetOrPutResult = struct {
            value_ptr: *V,
            found_existing: bool,
        };

        /// If key exists this function cannot fail.
        /// If there is an existing item with `key`, then the result's
        /// `value_pointer` point to it, and found_existing is true.
        /// Otherwise, puts a new item with undefined value, and
        /// the `value_pointer` point to it. Caller should then initialize
        /// the value.
        pub fn getOrPut(self: *@This(), k: K) AllocError!GetOrPutResult {
            var parent: *Node = self.root orelse {
                std.debug.assert(self.count == 0);
                self.root = try self.alloc.create(Node);
                self.root.?.* = .{ .color = .Black, .key = k, .value = undefined };
                self.count = 1;
                return .{ .value_ptr = &self.root.?.value, .found_existing = false };
            };

            const which: enum { left, right } = while (true) {
                switch (if (@TypeOf(ctx) == void) comp_fn(k, parent.key) else comp_fn(k, parent.key, ctx)) {
                    .eq => {
                        return .{ .value_ptr = &parent.value, .found_existing = true };
                    },
                    .lt => parent = parent.left orelse break .left,
                    .gt => parent = parent.right orelse break .right,
                }
            };

            var node: *Node = try self.alloc.create(Node);
            (switch (which) {
                .left => parent.left,
                .right => parent.right,
            }) = node;

            node.* = .{ .parent = parent, .key = k, .value = undefined };
            self.count += 1;

            node.balanceInsert();

            if (self.root.?.parent) |p| self.root = p;

            return .{ .value_ptr = &node.value, .found_existing = false };
        }

        pub fn getOrPutValue(self: *@This(), k: K, v: V) AllocError!*V {
            const res = (try self.getOrPut(k));
            if (!res.found_existing) res.value_ptr.* = v;
            return res.value_ptr;
        }

        /// Inserts a new entry into the map, returning the previous value, if any.
        pub fn fetchPut(self: *@This(), k: K, v: V) AllocError!?V {
            const result: GetOrPutResult = try self.getOrPut(k);
            defer result.value_ptr.* = v;

            if (result.found_existing) {
                return result.value_ptr.*;
            }

            return null;
        }

        /// Clobbers any existing data. To detect if a put would clobber
        /// existing data, see `getOrPut`.
        pub fn put(self: *@This(), k: K, v: V) AllocError!void {
            (try self.getOrPut(k)).value_ptr.* = v;
        }

        /// Inserts a key-value pair into the map, asserting that no previous
        /// entry with the same key is already present
        pub fn putNoClobber(self: *@This(), k: K, v: V) AllocError!void {
            std.debug.assert(try self.fetchPut(k, v) == null);
        }

        pub fn removeNode(self: *@This(), node: *Node) void {
            const replacement: ?*Node = node.delete(self.alloc);
            self.count -= 1;
            if (self.root == node) {
                self.root = replacement orelse null;
                if (replacement == null) return;
            }

            if (self.root.?.parent) |p| {
                self.root = p;
            }
            if (self.root.?.parent) |p| {
                self.root = p;
                std.debug.assert(p.parent == null);
            }
        }

        pub fn fetchRemove(self: *@This(), k: K) ?V {
            const node: *Node = self.getNode(k) orelse return null;
            defer self.removeNode(node);
            return node.value;
        }

        /// Removes a value from the map and returns the removed value.
        pub fn remove(self: *@This(), k: K) bool {
            return self.fetchRemove(k) != null;
        }


        /// Create an iterator over the entries in the map.
        /// The iterator is invalidated if the map is modified.
        pub fn iterator(self: *@This()) Iterator {
            return .{ .p = self.getFirstNode() };
        }

        /// Set the map to an empty state, making deinitialization a no-op, and
        /// returning a copy of the original.
        pub fn move(self: *@This()) @This() {
            defer self.* = .{ .alloc = self.alloc };
            return self.*;
        }

        pub fn clone(self: *@This()) AllocError!@This() {
            if (self.count == 0) return .{ .alloc = self.alloc };

            var ret: @This() = .{ .root = try self.alloc.create(Node), .alloc = self.alloc, .count = self.count };
            ret.root.?.key = self.root.?.key;
            ret.root.?.value = self.root.?.value;
            ret.root.?.color = self.root.?.color;
            ret.root.?.parent = null;
            ret.root.?.left = null;
            ret.root.?.right = null;
            errdefer ret.deinit();

            var old_node: *Node = self.root.?;
            var new_node: *Node = ret.root.?;
            while (true) {
                if (new_node.left == null) {
                    if (old_node.left) |o| {
                        std.debug.assert(o.parent == old_node);
                        new_node.left = try self.alloc.create(Node);
                        new_node.left.?.key = o.key;
                        new_node.left.?.value = o.value;
                        new_node.left.?.color = o.color;
                        new_node.left.?.parent = new_node;
                        new_node.left.?.left = null;
                        new_node.left.?.right = null;

                        old_node = o;
                        new_node = new_node.left.?;
                        continue;
                    }
                }
                if (new_node.right == null) {
                    if (old_node.right) |o| {
                        std.debug.assert(o.parent == old_node);
                        new_node.right = try self.alloc.create(Node);
                        new_node.right.?.key = o.key;
                        new_node.right.?.value = o.value;
                        new_node.right.?.color = o.color;
                        new_node.right.?.parent = new_node;
                        new_node.right.?.left = null;
                        new_node.right.?.right = null;

                        old_node = o;
                        new_node = new_node.right.?;
                        continue;
                    }
                }

                if (new_node.parent) |p| {
                    new_node = p;
                    old_node = old_node.parent.?;
                } else break;
            }

            return ret;
        }
    };
}

pub fn AutoOrderedMap(comptime K: type, comptime V: type) type {
    return OrderedMap(K, V, {}, std.math.order);
}

pub fn OrderedStringMap(comptime V: type) type {
    const compFn = struct {
        fn f(a: []const u8, b: []const u8) std.math.Order {
            return std.mem.order(u8, a, b);
        }
    };
    return OrderedMap([]const u8, V, {}, compFn.f);
}

const testing = std.testing;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

test "order" {
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    try map.put(59, 3);
    try map.put(89, 3);
    try map.put(2, 3);
    try map.put(1034, 3);
    try map.put(33, 3);
    try map.put(725, 3);
    try map.put(98, 3);

    var iter = map.iterator();
    var i: usize = 0;

    const e = [_]u32{ 2, 33, 59, 89, 98, 725, 1034 };
    while (iter.next()) |n| : (i += 1) {
        try expectEqual(n.key, e[i]);
    }

    try expectEqual(i, 7);
}

test "repeat put/remove" {
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    const limit = 20;
    var i: u32 = 0;
    while (i < limit) : (i += 1) {
        try map.put(i, i);
    }

    // Repeatedly delete/insert an entry without resizing the map.
    // Put to different keys so entries don't land in the just-freed slot.
    i = 0;
    while (i < 10 * limit) : (i += 1) {
        try testing.expect(map.remove(i));
        if (i % 2 == 0) {
            try map.put(limit + i, i);
        } else {
            try map.put(limit + i, i);
        }
    }

    i = 9 * limit;
    while (i < 10 * limit) : (i += 1) {
        try expectEqual(map.get(limit + i), i);
    }

    //try expectEqual(map.unmanaged.count, limit);
}

test "deque" {
    const K = struct {
        dist: u32,
        coor: struct { usize, usize },

        fn lt(a: @This(), b: @This()) std.math.Order {
            switch (std.math.order(a.dist, b.dist)) {
                .lt, .gt => |v| return v,
                .eq => {},
            }
            switch (std.math.order(a.coor[0], b.coor[0])) {
                .lt, .gt => |v| return v,
                .eq => {},
            }
            return std.math.order(a.coor[1], b.coor[1]);
        }
        pub fn jsonStringify(self: *const @This(), writeStream: anytype) !void {
            const buf = std.fmt.allocPrint(testing.allocator, "{d},{d},{d}", .{ self.dist, self.coor[0], self.coor[1] }) catch "";
            defer testing.allocator.free(buf);
            return writeStream.write(buf);
        }
    };

    var queue: OrderedMap(K, void, {}, K.lt) = .{ .alloc = testing.allocator };
    defer queue.deinit();

    try queue.put(.{ .dist = 0, .coor = .{ 0, 0 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 2, .coor = .{ 1, 0 } }, {});
    try queue.put(.{ .dist = 2, .coor = .{ 0, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 6, .coor = .{ 1, 1 } }, {});
    try queue.put(.{ .dist = 6, .coor = .{ 0, 2 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 5, .coor = .{ 2, 0 } }, {});
    _ = queue.remove(.{ .dist = 6, .coor = .{ 1, 1 } });
    try queue.put(.{ .dist = 5, .coor = .{ 1, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 7, .coor = .{ 2, 1 } }, {});
    try queue.put(.{ .dist = 7, .coor = .{ 1, 2 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 8, .coor = .{ 3, 0 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 7, .coor = .{ 0, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 10, .coor = .{ 1, 3 } }, {});
    try queue.put(.{ .dist = 10, .coor = .{ 0, 4 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 8, .coor = .{ 2, 2 } }, {});
    _ = queue.remove(.{ .dist = 10, .coor = .{ 1, 3 } });
    try queue.put(.{ .dist = 8, .coor = .{ 1, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 9, .coor = .{ 3, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 13, .coor = .{ 2, 3 } }, {});
    try queue.put(.{ .dist = 13, .coor = .{ 1, 4 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 13, .coor = .{ 3, 2 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 11, .coor = .{ 4, 0 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 13, .coor = .{ 4, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 14, .coor = .{ 0, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 15, .coor = .{ 5, 0 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 17, .coor = .{ 2, 4 } }, {});
    try queue.put(.{ .dist = 17, .coor = .{ 1, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 18, .coor = .{ 3, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 17, .coor = .{ 4, 2 } }, {});
    _ = queue.remove(.{ .dist = 18, .coor = .{ 3, 3 } });
    try queue.put(.{ .dist = 17, .coor = .{ 3, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 18, .coor = .{ 5, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 17, .coor = .{ 0, 6 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 16, .coor = .{ 6, 0 } }, {});
    _ = queue.remove(.{ .dist = 18, .coor = .{ 5, 1 } });
    try queue.put(.{ .dist = 16, .coor = .{ 5, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 20, .coor = .{ 6, 1 } }, {});
    try queue.put(.{ .dist = 20, .coor = .{ 5, 2 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 20, .coor = .{ 7, 0 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 19, .coor = .{ 1, 6 } }, {});
    try queue.put(.{ .dist = 19, .coor = .{ 0, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 22, .coor = .{ 2, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 19, .coor = .{ 3, 4 } }, {});
    _ = queue.remove(.{ .dist = 22, .coor = .{ 2, 5 } });
    try queue.put(.{ .dist = 19, .coor = .{ 2, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 23, .coor = .{ 4, 3 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 23, .coor = .{ 4, 3 } });
    try queue.put(.{ .dist = 21, .coor = .{ 4, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 22, .coor = .{ 1, 7 } }, {});
    try queue.put(.{ .dist = 22, .coor = .{ 0, 8 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 22, .coor = .{ 2, 6 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 23, .coor = .{ 3, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 24, .coor = .{ 4, 4 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 23, .coor = .{ 6, 2 } }, {});
    try queue.put(.{ .dist = 23, .coor = .{ 5, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 24, .coor = .{ 7, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 23, .coor = .{ 8, 0 } }, {});
    _ = queue.remove(.{ .dist = 24, .coor = .{ 7, 1 } });
    try queue.put(.{ .dist = 23, .coor = .{ 7, 1 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 23, .coor = .{ 1, 8 } }, {});
    try queue.put(.{ .dist = 23, .coor = .{ 0, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 27, .coor = .{ 2, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 27, .coor = .{ 3, 6 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 24, .coor = .{ 1, 9 } }, {});
    try queue.put(.{ .dist = 24, .coor = .{ 0, 10 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 26, .coor = .{ 2, 8 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 31, .coor = .{ 4, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 31, .coor = .{ 6, 3 } }, {});
    try queue.put(.{ .dist = 31, .coor = .{ 5, 4 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 28, .coor = .{ 7, 2 } }, {});
    _ = queue.remove(.{ .dist = 31, .coor = .{ 6, 3 } });
    try queue.put(.{ .dist = 28, .coor = .{ 6, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 29, .coor = .{ 8, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 27, .coor = .{ 9, 0 } }, {});
    _ = queue.remove(.{ .dist = 29, .coor = .{ 8, 1 } });
    try queue.put(.{ .dist = 27, .coor = .{ 8, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 27, .coor = .{ 1, 10 } }, {});
    try queue.put(.{ .dist = 27, .coor = .{ 0, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 29, .coor = .{ 2, 9 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 31, .coor = .{ 5, 4 } });
    try queue.put(.{ .dist = 30, .coor = .{ 5, 4 } }, {});
    _ = queue.remove(.{ .dist = 31, .coor = .{ 4, 5 } });
    try queue.put(.{ .dist = 30, .coor = .{ 4, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 31, .coor = .{ 3, 8 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 29, .coor = .{ 1, 11 } }, {});
    try queue.put(.{ .dist = 29, .coor = .{ 0, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 33, .coor = .{ 2, 10 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 33, .coor = .{ 3, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 32, .coor = .{ 4, 6 } }, {});
    _ = queue.remove(.{ .dist = 33, .coor = .{ 3, 7 } });
    try queue.put(.{ .dist = 32, .coor = .{ 3, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 33, .coor = .{ 9, 1 } }, {});
    try queue.put(.{ .dist = 33, .coor = .{ 8, 2 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 31, .coor = .{ 10, 0 } }, {});
    _ = queue.remove(.{ .dist = 33, .coor = .{ 9, 1 } });
    try queue.put(.{ .dist = 31, .coor = .{ 9, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 35, .coor = .{ 7, 3 } }, {});
    try queue.put(.{ .dist = 35, .coor = .{ 6, 4 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 33, .coor = .{ 8, 2 } });
    try queue.put(.{ .dist = 31, .coor = .{ 8, 2 } }, {});
    _ = queue.remove(.{ .dist = 35, .coor = .{ 7, 3 } });
    try queue.put(.{ .dist = 31, .coor = .{ 7, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 32, .coor = .{ 1, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 31, .coor = .{ 2, 11 } }, {});
    _ = queue.remove(.{ .dist = 32, .coor = .{ 1, 12 } });
    try queue.put(.{ .dist = 31, .coor = .{ 1, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 33, .coor = .{ 3, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 35, .coor = .{ 5, 5 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 34, .coor = .{ 2, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 36, .coor = .{ 3, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 35, .coor = .{ 4, 8 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 38, .coor = .{ 8, 3 } }, {});
    try queue.put(.{ .dist = 38, .coor = .{ 7, 4 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 36, .coor = .{ 9, 2 } }, {});
    _ = queue.remove(.{ .dist = 38, .coor = .{ 8, 3 } });
    try queue.put(.{ .dist = 36, .coor = .{ 8, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 36, .coor = .{ 10, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 32, .coor = .{ 11, 0 } }, {});
    _ = queue.remove(.{ .dist = 36, .coor = .{ 10, 1 } });
    try queue.put(.{ .dist = 32, .coor = .{ 10, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 40, .coor = .{ 4, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 39, .coor = .{ 5, 6 } }, {});
    _ = queue.remove(.{ .dist = 40, .coor = .{ 4, 7 } });
    try queue.put(.{ .dist = 39, .coor = .{ 4, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 34, .coor = .{ 11, 1 } }, {});
    try queue.put(.{ .dist = 34, .coor = .{ 10, 2 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 34, .coor = .{ 12, 0 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 35, .coor = .{ 3, 10 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 38, .coor = .{ 4, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 38, .coor = .{ 3, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 36, .coor = .{ 11, 2 } }, {});
    try queue.put(.{ .dist = 36, .coor = .{ 10, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 39, .coor = .{ 12, 1 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 39, .coor = .{ 12, 1 } });
    try queue.put(.{ .dist = 38, .coor = .{ 12, 1 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 39, .coor = .{ 4, 10 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 41, .coor = .{ 5, 8 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 44, .coor = .{ 6, 5 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 44, .coor = .{ 6, 5 } });
    try queue.put(.{ .dist = 43, .coor = .{ 6, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 41, .coor = .{ 4, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 40, .coor = .{ 9, 3 } }, {});
    try queue.put(.{ .dist = 40, .coor = .{ 8, 4 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 40, .coor = .{ 11, 3 } }, {});
    try queue.put(.{ .dist = 40, .coor = .{ 10, 4 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 40, .coor = .{ 12, 2 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 40, .coor = .{ 4, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 45, .coor = .{ 5, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 46, .coor = .{ 7, 5 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 47, .coor = .{ 5, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 44, .coor = .{ 5, 10 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 47, .coor = .{ 6, 6 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 46, .coor = .{ 5, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 49, .coor = .{ 9, 4 } }, {});
    try queue.put(.{ .dist = 49, .coor = .{ 8, 5 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 49, .coor = .{ 9, 4 } });
    try queue.put(.{ .dist = 44, .coor = .{ 9, 4 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 46, .coor = .{ 11, 4 } }, {});
    try queue.put(.{ .dist = 46, .coor = .{ 10, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 46, .coor = .{ 12, 3 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 46, .coor = .{ 12, 3 } });
    try queue.put(.{ .dist = 42, .coor = .{ 12, 3 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 44, .coor = .{ 5, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 50, .coor = .{ 6, 8 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 44, .coor = .{ 12, 4 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 48, .coor = .{ 6, 10 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 49, .coor = .{ 6, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 50, .coor = .{ 9, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 50, .coor = .{ 12, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 53, .coor = .{ 6, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 50, .coor = .{ 6, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 53, .coor = .{ 7, 6 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 54, .coor = .{ 11, 5 } }, {});
    try queue.put(.{ .dist = 54, .coor = .{ 10, 6 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 54, .coor = .{ 11, 5 } });
    try queue.put(.{ .dist = 51, .coor = .{ 11, 5 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 54, .coor = .{ 6, 7 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 54, .coor = .{ 6, 7 } });
    try queue.put(.{ .dist = 53, .coor = .{ 6, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 55, .coor = .{ 7, 10 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 55, .coor = .{ 7, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 55, .coor = .{ 8, 6 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 58, .coor = .{ 7, 8 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 56, .coor = .{ 7, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 57, .coor = .{ 9, 6 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 57, .coor = .{ 12, 6 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 55, .coor = .{ 11, 6 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 62, .coor = .{ 7, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 60, .coor = .{ 7, 9 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 62, .coor = .{ 7, 7 } });
    try queue.put(.{ .dist = 60, .coor = .{ 7, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 60, .coor = .{ 10, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 61, .coor = .{ 8, 10 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 60, .coor = .{ 8, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 62, .coor = .{ 8, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 63, .coor = .{ 11, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 59, .coor = .{ 8, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 66, .coor = .{ 9, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 61, .coor = .{ 12, 7 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 65, .coor = .{ 8, 8 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 66, .coor = .{ 9, 12 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 69, .coor = .{ 8, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 68, .coor = .{ 9, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 68, .coor = .{ 10, 8 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 69, .coor = .{ 9, 10 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 67, .coor = .{ 12, 8 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 71, .coor = .{ 11, 8 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 73, .coor = .{ 9, 8 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 69, .coor = .{ 10, 12 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 72, .coor = .{ 12, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 73, .coor = .{ 10, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 74, .coor = .{ 10, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 75, .coor = .{ 9, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 73, .coor = .{ 10, 10 } }, {});
    _ = queue.remove(.{ .dist = 75, .coor = .{ 9, 9 } });
    try queue.put(.{ .dist = 73, .coor = .{ 9, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 72, .coor = .{ 11, 12 } }, {});
    _ = queue.remove(.{ .dist = 73, .coor = .{ 10, 11 } });
    try queue.put(.{ .dist = 72, .coor = .{ 10, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 79, .coor = .{ 11, 9 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 78, .coor = .{ 11, 11 } }, {});
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 77, .coor = .{ 12, 12 } }, {});
    _ = queue.remove(.{ .dist = 78, .coor = .{ 11, 11 } });
    try queue.put(.{ .dist = 77, .coor = .{ 11, 11 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.remove(.{ .dist = 79, .coor = .{ 11, 9 } });
    try queue.put(.{ .dist = 77, .coor = .{ 11, 9 } }, {});
    try queue.put(.{ .dist = 77, .coor = .{ 12, 10 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 78, .coor = .{ 11, 10 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    try queue.put(.{ .dist = 80, .coor = .{ 12, 11 } }, {});
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
    _ = queue.dequeWithKey();
}

test "basic usage" {
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    const count = 5;
    var i: u32 = 0;
    var total: u32 = 0;
    while (i < count) : (i += 1) {
        try map.put(i, i);
        total += i;
    }

    var sum: u32 = 0;
    var it = map.iterator();
    while (it.next()) |kv| {
        sum += kv.key;
    }
    try expectEqual(total, sum);

    i = 0;
    sum = 0;
    while (i < count) : (i += 1) {
        try expectEqual(i, map.get(i).?);
        sum += map.get(i).?;
    }
    try expectEqual(total, sum);
}

test "clone" {
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    var a = try map.clone();
    defer a.deinit();

    try expectEqual(a.count, 0);

    try a.put(1, 1);
    try a.put(2, 2);
    try a.put(3, 3);

    var b = try a.clone();
    defer b.deinit();

    try expectEqual(b.count, 3);
    try expectEqual(b.get(1).?, 1);
    try expectEqual(b.get(2).?, 2);
    try expectEqual(b.get(3).?, 3);

    var original = AutoOrderedMap(i32, i32){ .alloc = std.testing.allocator };
    defer original.deinit();

    var i: u8 = 0;
    while (i < 10) : (i += 1) {
        try original.putNoClobber(i, i * 10);
    }

    var copy = try original.clone();
    defer copy.deinit();

    i = 0;
    while (i < 10) : (i += 1) {
        try testing.expect(copy.get(i).? == i * 10);
    }
}

test "remove" {
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        if (i % 3 == 0) {
            _ = map.remove(i);
        }
    }
    try expectEqual(map.count, 10);
    var it = map.iterator();
    while (it.next()) |kv| {
        try expectEqual(kv.key, kv.value);
        try expect(kv.key % 3 != 0);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        if (i % 3 == 0) {
            try expect(!map.contains(i));
        } else {
            try expectEqual(map.get(i).?, i);
        }
    }
}

test "reverse removes" {
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.putNoClobber(i, i);
    }

    i = 16;
    while (i > 0) : (i -= 1) {
        _ = map.remove(i - 1);
        try expect(!map.contains(i - 1));
        var j: u32 = 0;
        while (j < i - 1) : (j += 1) {
            try expectEqual(map.get(j).?, j);
        }
    }

    try expectEqual(map.count, 0);
}

test "multiple removes on same metadata" {
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i);
    }

    _ = map.remove(7);
    _ = map.remove(15);
    _ = map.remove(14);
    _ = map.remove(13);
    try expect(!map.contains(7));
    try expect(!map.contains(15));
    try expect(!map.contains(14));
    try expect(!map.contains(13));

    i = 0;
    while (i < 13) : (i += 1) {
        if (i == 7) {
            try expect(!map.contains(i));
        } else {
            try expectEqual(map.get(i).?, i);
        }
    }

    try map.put(15, 15);
    try map.put(13, 13);
    try map.put(14, 14);
    try map.put(7, 7);
    i = 0;
    while (i < 16) : (i += 1) {
        try expectEqual(map.get(i).?, i);
    }
}

test "put and remove loop in random order" {
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    var keys = std.ArrayList(u32).init(std.testing.allocator);
    defer keys.deinit();

    const size = 32;
    const iterations = 100;

    var i: u32 = 0;
    while (i < size) : (i += 1) {
        try keys.append(i);
    }
    var prng = std.Random.DefaultPrng.init(0);
    const random = prng.random();

    while (i < iterations) : (i += 1) {
        random.shuffle(u32, keys.items);

        for (keys.items) |key| {
            try map.put(key, key);
        }
        try expectEqual(map.count, size);

        for (keys.items) |key| {
            _ = map.remove(key);
        }
        try expectEqual(map.count, 0);
    }
}

test "remove one million elements in random order" {
    const n = 1000 * 1000;
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    var keys = std.ArrayList(u32).init(std.heap.page_allocator);
    defer keys.deinit();

    var i: u32 = 0;
    while (i < n) : (i += 1) {
        keys.append(i) catch unreachable;
    }

    var prng = std.Random.DefaultPrng.init(0);
    const random = prng.random();
    random.shuffle(u32, keys.items);

    for (keys.items) |key| {
        map.put(key, key) catch unreachable;
    }

    random.shuffle(u32, keys.items);
    i = 0;
    while (i < n) : (i += 1) {
        const key = keys.items[i];
        _ = map.remove(key);
    }
}

test "put" {
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        try expectEqual(map.get(i).?, i);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i * 16 + 1);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        try expectEqual(map.get(i).?, i * 16 + 1);
    }
}

test "getOrPut" {
    var map = AutoOrderedMap(u32, u32){ .alloc = std.testing.allocator };
    defer map.deinit();

    var i: u32 = 0;
    while (i < 10) : (i += 1) {
        try map.put(i * 2, 2);
    }

    i = 0;
    while (i < 20) : (i += 1) {
        _ = try map.getOrPutValue(i, 1);
    }

    i = 0;
    var sum = i;
    while (i < 20) : (i += 1) {
        sum += map.get(i).?;
    }

    try expectEqual(sum, 30);
}

test "basic map usage" {
    var map = AutoOrderedMap(i32, i32){ .alloc = std.testing.allocator };
    defer map.deinit();

    try testing.expect((try map.fetchPut(1, 11)) == null);
    try testing.expect((try map.fetchPut(2, 22)) == null);
    try testing.expect((try map.fetchPut(3, 33)) == null);
    try testing.expect((try map.fetchPut(4, 44)) == null);

    try map.putNoClobber(5, 55);
    try testing.expect((try map.fetchPut(5, 66)).? == 55);
    try testing.expect((try map.fetchPut(5, 55)).? == 66);

    const gop1 = try map.getOrPut(5);
    try testing.expect(gop1.found_existing == true);
    try testing.expect(gop1.value_ptr.* == 55);
    gop1.value_ptr.* = 77;
    try testing.expect(map.getNode(5).?.value == 77);

    const gop2 = try map.getOrPut(99);
    try testing.expect(gop2.found_existing == false);
    gop2.value_ptr.* = 42;
    try testing.expect(map.getNode(99).?.value == 42);

    const gop3 = try map.getOrPutValue(5, 5);
    try testing.expect(gop3.* == 77);

    const gop4 = try map.getOrPutValue(100, 41);
    try testing.expect(gop4.* == 41);

    try testing.expect(map.contains(2));
    try testing.expect(map.getNode(2).?.value == 22);
    try testing.expect(map.get(2).? == 22);

    const rmv1 = map.fetchRemove(2);
    try testing.expect(rmv1.? == 22);
    try testing.expect(map.fetchRemove(2) == null);
    try testing.expect(map.remove(2) == false);
    try testing.expect(map.getNode(2) == null);
    try testing.expect(map.get(2) == null);

    try testing.expect(map.remove(3) == true);
}

test "removeNode" {
    var map = AutoOrderedMap(i32, u64){ .alloc = testing.allocator };
    defer map.deinit();

    var i: i32 = undefined;

    i = 0;
    while (i < 10) : (i += 1) {
        try map.put(i, 0);
    }

    try testing.expect(map.count == 10);

    i = 0;
    while (i < 10) : (i += 1) {
        const node_ptr = map.getNode(i);
        try testing.expect(node_ptr != null);

        if (node_ptr) |ptr| {
            map.removeNode(ptr);
        }
    }

    try testing.expect(map.count == 0);
}

test "removeNode 0 sized key" {
    var map = AutoOrderedMap(u0, u64){ .alloc = testing.allocator };
    defer map.deinit();

    try map.put(0, 0);

    try testing.expect(map.count == 1);

    const key_ptr = map.getNode(0);
    try testing.expect(key_ptr != null);

    if (key_ptr) |ptr| {
        map.removeNode(ptr);
    }

    try testing.expect(map.count == 0);
}

test "repeat fetchRemove" {
    var map = AutoOrderedMap(u64, void){ .alloc = std.testing.allocator };
    defer map.deinit();

    try map.put(0, {});
    try map.put(1, {});
    try map.put(2, {});
    try map.put(3, {});

    // fetchRemove() should make slots available.
    var i: usize = 0;
    while (i < 10) : (i += 1) {
        try testing.expect(map.fetchRemove(3) != null);
        try map.put(3, {});
    }

    try testing.expect(map.get(0) != null);
    try testing.expect(map.get(1) != null);
    try testing.expect(map.get(2) != null);
    try testing.expect(map.get(3) != null);
}

test "getOrPut allocation failure" {
    var map = OrderedStringMap(void){ .alloc = std.testing.failing_allocator };
    try testing.expectError(error.OutOfMemory, map.getOrPut("hello"));
}
