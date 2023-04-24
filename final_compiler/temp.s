L186: .asciiz "\n"
L185:
move $s7, $s7
move $s6, $s6
move $s5, $s5
move $s4, $s4
move $s3, $s3
move $s2, $s2
move $s1, $s1
move $s0, $s0
L188:
la $v0, L186
move $a0, $v0
jal L132
move $v0, $v0
j L187
L187:
move $s0, $s0
move $s1, $s1
move $s2, $s2
move $s3, $s3
move $s4, $s4
move $s5, $s5
move $s6, $s6
move $s7, $s7
jr $ra
L184:
move $v0, $s7
sw $v0, -4($fp)
move $s7, $s6
move $s6, $s5
move $s5, $s4
move $s4, $s3
move $s2, $s2
move $s1, $s1
move $s0, $s0

L189:
move $s0, $s0
move $s1, $s1
move $s2, $s2
move $s3, $s4
move $s4, $s5
move $s5, $s6
move $s6, $s7
lw $v0, -4($fp)
move $s7, $v0
jr $ra
