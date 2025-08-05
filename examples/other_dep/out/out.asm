.text
.globl _main
_main:
s0i1:
	adrp x1, str0@PAGE
	add x1, x1, str0@PAGEOFF
	mov x2, x1
	bl s0i0
	mov x3, x0
	neg x3, x3
	mov x5, #53
	mov x4, #2
	mul x4, x5, x4
	add x6, x3, x4
	mov x7, x6
	adrp x8, fl1@PAGE
	ldr s9, [x8, fl1@PAGEOFF]
	adrp x10, fl2@PAGE
	ldr s11, [x10, fl2@PAGEOFF]
	fmov s12, s11
	fmul s12, s9, s12
	adrp x13, fl3@PAGE
	ldr s14, [x13, fl3@PAGEOFF]
	fsub s15, s12, s14
	fmov s16, s15
	mov x17, #0
	fcvtzs x17, s16
	add x18, x17, x7
	mov x17, x18
	mov x19, x0
	mov x20, x2
	
    mov x0, 1
    mov x2, 5
    mov x16, 4
    svc 0
    
	mov x0, x19
	mov x2, x20
	mov x21, x0
	
    mov x0, x17
    mov x16, 1
    svc 0
    
	mov x0, x21
s0i0:
	mov x0, #2
	ret
.data
.balign 4
str0: .string "hello"
.balign 4
fl1: .float 2.593
.balign 4
fl2: .float 4.2
.balign 4
fl3: .float 20
