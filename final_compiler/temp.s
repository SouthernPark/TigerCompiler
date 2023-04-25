L76: .asciiz "\n"
L75:
sw $fp, -4($sp)
move $fp, $sp
addi $sp, $sp, -56
L78:
sw $a0, 0($fp)
move $s7, $s7
move $s6, $s6
move $s5, $s5
move $s4, $s4
move $s3, $s3
move $s2, $s2
move $s1, $s1
move $s0, $s0
la $v0, L76
move $a0, $v0
jal L64
move $v0, $v0
move $s0, $s0
move $s1, $s1
move $s2, $s2
move $s3, $s3
move $s4, $s4
move $s5, $s5
move $s6, $s6
move $s7, $s7
j L77
L77:
move $sp, $fp
lw $fp, -4($fp)
jr $ra
L74:
sw $fp, -4($sp)
move $fp, $sp
addi $sp, $sp, -56
L80:
sw $a0, 0($fp)
move $v0, $s7
sw $v0, -4($fp)
move $s7, $s6
move $s6, $s5
move $s5, $s4
move $s4, $s3
move $s2, $s2
move $s1, $s1
move $s0, $s0
li $s3, 8
addi $v0, $s3, 1
move $a0, $v0
li $a1, 0
jal initArray
move $v0, $v0
sw $s3, 0($v0) 
addi $v0, $v0, 4
move $v0, $v0
move $v0, $v0
move $a0, $fp
jal L75
move $v0, $v0
move $s0, $s0
move $s1, $s1
move $s2, $s2
move $s3, $s4
move $s4, $s5
move $s5, $s6
move $s6, $s7
lw $v0, -4($fp)
move $s7, $v0
j L79
L79:
move $sp, $fp
lw $fp, -4($fp)
jr $ra
