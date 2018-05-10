const std = @import("std");
const BigInt = @import("../bigint.zig").BigInt;

const target = 50000;

pub fn main() !void {
    var stdout_file = try std.io.getStdOut();
    var allocator = std.heap.c_allocator;

    var f = try BigInt.initSet(allocator, 1);
    var c = try BigInt.initSet(allocator, 1);
    var one = try BigInt.initSet(allocator, 1);

    var i: usize = 0;
    while (i < target) : (i += 1) {
        try f.mul(&f, &c);
        try c.add(&c, &one);
    }

    const r = try f.toString(allocator, 16);
    try stdout_file.write(r);
}
