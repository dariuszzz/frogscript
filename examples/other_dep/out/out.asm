.text
.globl _main
_main:
	b s0i1
s0i0:
	stp fp, lr, [sp,#-16]!
	mov fp, sp
	sub sp, sp, #16
	mov x1, x0
	mov x3, #2
	mul x2, x1, x3
	mov x0, x2
	mov sp, fp
	ldp fp, lr, [sp], #16
	ret
s0i1:
	stp fp, lr, [sp,#-16]!
	mov fp, sp
	sub sp, sp, #16
	mov x4, #100
	mov x0, x4
	bl s0i0
	mov x5, x0
	
    mov x0, x5
    mov x16, 1
    svc 0
    
	mov x0, x5
