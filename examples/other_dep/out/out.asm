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
	mov x4, x3
	mov x5, x0
	mov x6, x2
	
    mov x0, 1
    mov x2, 5
    mov x16, 4
    svc 0
    
	mov x0, x5
	mov x2, x6
	mov x7, x0
	
    mov x0, x4
    mov x16, 1
    svc 0
    
	mov x0, x7
s0i0:
	mov x0, 2
	ret
.data
	str0: .string "siema"
