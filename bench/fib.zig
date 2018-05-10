const std = @import("std");
const BigInt = @import("../bigint.zig").BigInt;

const target = 200000;

pub fn main() !void {
    var stdout_file = try std.io.getStdOut();
    var allocator = std.heap.c_allocator;

    var f0 = try BigInt.initSet(allocator, 1);
    var f1 = try BigInt.initSet(allocator, 1);

    var i: usize = 0;
    while (i < target) : (i += 1) {
        try f1.add(&f1, &f0);
        try f0.sub(&f1, &f0);
    }

    const r = try f1.toString(allocator, 16);
    try stdout_file.write(r);
}
