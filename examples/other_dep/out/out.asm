.text
.globl _main
_main:
	b s0i1
s0i0:
	mov x0, #2
	ret
s0i1:
	adrp x1, str0@PAGE
	add x1, x1, str0@PAGEOFF
	mov x2, x1
	mov x3, #3
	mov x4, 0
	b false_4
true_3:
	adrp x5, str1@PAGE
	add x5, x5, str1@PAGEOFF
	mov x2, x5
	b merge_2
false_4:
	adrp x6, str2@PAGE
	add x6, x6, str2@PAGEOFF
	mov x2, x6
	b merge_2
merge_2:
	mov x7, x1
	mov x8, x2
	
    mov x0, 1
    mov x1, x8
    mov x2, 3
    mov x16, 4
    svc 0
    
	mov x1, x7
	mov x2, x8
	
    mov x0, 0
    mov x16, 1
    svc 0
    
.data
.balign 4
str0: .string "bobas"
.balign 4
str1: .string "git"
.balign 4
str2: .string "huj"
