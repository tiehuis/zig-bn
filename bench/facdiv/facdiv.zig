const std = @import("std");
const Int = @import("../../int.zig").Int;

const target = 20000;

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

    const ss1 = try f.toString(allocator, 16);
    try stdout_file.write(ss1);
    try stdout_file.write(" ");

    var r = try Int.init(allocator);

    i = target - 1;
    while (i != 0) : (i -= 1) {
        try c.sub(&c, 1);
        try f.div(&r, &f, &c);
    }

    const ss = try f.toString(allocator, 16);
    try stdout_file.write(ss);
}
