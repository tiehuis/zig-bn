const std = @import("std");
const Int = @import("../../int.zig").Int;

const target = 50000;

pub fn main() !void {
    var stdout_file = try std.io.getStdOut();
    var allocator = std.heap.c_allocator;

    var f = try Int.initSet(allocator, 1);
    var c = try Int.initSet(allocator, 1);

    var i: usize = 0;
    while (i < target) : (i += 1) {
        try f.mul(&f, &c);
        try c.add(&c, 1);
    }

    const r = try f.toString(allocator, 16);
    try stdout_file.write(r);
}
