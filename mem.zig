/// A local fixed memory allocator for function-local small allocations. Think of this as a an
/// alloca-like equivalent.
///
/// Items allocated with this allocator should be de-allocated in order. If multiple items are
/// allocated at once, the order doesn't matter, as long as no usage occurs between deallocations.

const mem = @import("std").mem;

pub var stack_allocator = mem.Allocator {
    .allocFn = stackAlloc,
    .reallocFn = stackRealloc,
    .freeFn = stackFree,
};

error OutOfMemory;

var stack_mem: [512]u8 = undefined;
var stack_mem_index: usize = 0;

fn stackAlloc(self: &mem.Allocator, n: usize) -> %[]u8 {
    if (stack_mem_index + n > stack_mem.len) {
        return error.OutOfMemory;
    }

    const result = stack_mem[stack_mem_index .. stack_mem_index + n];
    stack_mem_index += n;
    return result;
}

fn stackRealloc(self: &mem.Allocator, old_mem: []u8, new_size: usize) -> %[]u8 {
    // cannot reallocate a stack-allocated region (could if it was last item).
    error.OutOfMemory
}

fn stackFree(self: &mem.Allocator, old_mem: []u8) {
    if (old_mem.len > stack_mem_index) {
        @panic("stack underflow during free\n");
    }

    stack_mem_index -= old_mem.len;
}
