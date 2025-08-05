
.globl _main

_main:
s0i1:
	mov x1, 6
	bl s0i0
	mov x2, x0
	neg x2, x2
	mov x3, 3
	mul x3, x1, x3
	add x4, x2, x3
	mov x5, x4
	mov x0, x5
	mov x16, #1
	svc #0
s0i0:
	mov x0, 2
	ret
