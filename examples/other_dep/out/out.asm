.text
.globl _main
_main:
	b s0i1
s0i0:
	stp fp, lr, [sp,#-16]!
	mov fp, sp
	sub sp, sp, #160
	mov x0, #2
	mov sp, fp
	ldp fp, lr, [sp], #160
	ret
s0i1:
	stp fp, lr, [sp,#-16]!
	mov fp, sp
	sub sp, sp, #160
	// array
	mov x1, #4
	str x1, [fp,#-8]
	mov x2, #6
	str x2, [fp,#-16]
	add x3, fp, #-8
	mov x4, x3
	mov x5, x4
	// access
	mov x6, #1
	mov x7, x5
	mov x8, #8
	mul x6, x6, x8
	ldr x9, [fp,x6]
	mov x10, x9
	// print
	
    mov x0, x10
    mov x16, 1
    svc 0
    
