run:
	make -C fib run
	make -C fac run

build:
	make -C fib build
	make -C fac build

system: cpu version

cpu:
	@lscpu
	@printf "\n"

version:
	@printf "zig:  " && zig version
	@printf "gcc:  " && gcc --version | head -n1
	@printf "go:   " && go version
	@printf "py:   " && python3 --version
	@printf "rust: " && rustc --version

clean:
	make -C fib clean
	make -C fac clean

.PHONY: run build cpu clean version
