# zig-ordered-map
Ordered Map in Zig, with an interface similar to HashMap's

### Adding it to project

1. add it to the dependencies in `build.zig.zon`, so the zig build system can fetch it
```zig
.dependencies = .{
    .ordered_map=.{
        .url = "https://github.com/Mecso2/zig-ordered-map/archive/refs/heads/master.tar.gz",
        .hash = "ordered_map-1.0.1-OChsRPn0AAAHDReeqrkWKBMRb9NP5sgtCH6Qps0j2lVl"
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


pub fn main() !void {
    var gpa: std.heap.DebugAllocator(.{})=.{};

    var map: om.AutoOrderedMap(u32, u32)=.{.alloc = gpa.allocator()};
    defer map.deinit();

    try map.put(5, 39);
    stdout.debug.print("{?d}", .{map.get(5)});
}
```
