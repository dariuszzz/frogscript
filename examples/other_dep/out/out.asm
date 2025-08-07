.text
.globl _main
_main:
	b s0i1
s0i0:
	stp fp, lr, [sp,#-16]!
	mov fp, sp
	sub sp, sp, #16
	mov x0, #2
	mov sp, fp
	ldp fp, lr, [sp], #16
	ret
s0i1:
	stp fp, lr, [sp,#-16]!
	mov fp, sp
	sub sp, sp, #16
	adrp x1, fl0@PAGE
	ldr s2, [x1, fl0@PAGEOFF]
	fmov s3, s2
	str s3, [fp,#-8]
	adrp x4, fl1@PAGE
	ldr s5, [x4, fl1@PAGEOFF]
	fmov s6, s5
	str s6, [fp,#-16]
	add x7, fp, #-8
	mov x8, x7
	mov x9, #0
	mov x10, #-8
	mul x9, x9, x10
	add x9, x9, #-8
	adrp x11, fl2@PAGE
	ldr s12, [x11, fl2@PAGEOFF]
	fmov s13, s12
	str s13, [fp,x9]
	mov x14, #0
	mov x15, #-8
	mul x14, x14, x15
	add x14, x14, #-8
	ldr s16, [fp,x14]
	mov x17, #0
	fcvtzs x17, s16
	
    mov x0, x17
    mov x16, 1
    svc 0
    
.data
.balign 4
fl0: .float 4.42
.balign 4
fl1: .float 6.23
.balign 4
fl2: .float 2.59
