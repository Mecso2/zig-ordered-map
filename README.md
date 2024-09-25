# zig-ordered-map
Ordered Map in Zig, with an interface similar to HashMap's

### Adding it to project

1. add it to the dependencies in `build.zig.zon`, so the zig build system can fetch it
```zig
.dependencies = .{
    .ordered_map=.{
        .url = "https://github.com/Mecso2/zig-ordered-map/archive/refs/heads/master.tar.gz",
        .hash = "1220d160db858f5d7fd16d44922a5349cd7a39c791fc2d623ebdf2346b34b0ddd5f9"
    }
}
```
2. add the the module to your artifact in `build.zig`
```zig
exe.root_module.addImport("om", b.dependency("ordered_map", .{}).module("the"));
```
3. import it and use it
```zig
const std = @import("std");
const om = @import("om");
const stdout=std.io.getStdOut().writer();


pub fn main() !void {
    var gpa: std.heap.GeneralPurposeAllocator(.{})=.{};

    var map: om.AutoOrderedMap(u32, u32)=.{.alloc = gpa.allocator()};
    defer map.deinit();

    try map.put(5, 39);
    try stdout.print("{?d}", .{map.get(5)});
}
```
