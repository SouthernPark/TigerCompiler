L57: .asciiz "\n"
L51: .asciiz " ."
L50: .asciiz " O"
L44:
L61:
li $s1, 0
lw $v0, 0($fp)
lw $v1, -4($v0)
li $v0, 1
sub $v0, $v1, $v0
move $s0, $v0
ble $s1, $s0, L59
L45:
la $v0, L57
move $a0, $v0
jal L33
move $v0, $v0
j L60
L58:
addi $v0, $s1, 1
move $s1, $v0
L59:
li $s3, 0
lw $v0, 0($fp)
lw $v1, -4($v0)
li $v0, 1
sub $v0, $v1, $v0
move $s2, $v0
ble $s3, $s2, L56
L46:
la $v0, L57
move $a0, $v0
jal L33
blt $s1, $s0, L58
L62:
j L45
L55:
addi $v0, $s3, 1
move $s3, $v0
L56:
lw $v0, 0($fp)
lw $v0, -8($v0)
move $s4, $v0
move $s5, $s5
li $v0, 0
blt $s5, $v0, L47
L48:
li $v0, 1
sub $v0, $s4, $v0
lw $v0, 0($v0)
bge $s5, $v0, L47
L49:
li $v0, 4
mul $v0, $s5, $v0
add $v0, $s4, $v0
lw $v0, 0($v0)
beq $v0, $s6, L52
L53:
la $v0, L51
move $v0, $v0
L54:
move $a0, $v0
jal L33
blt $s3, $s2, L55
L63:
j L46
L47:
li $a0, 1
jal exit
j L49
L52:
la $v0, L50
move $v0, $v0
j L54
L60:
jr $ra
L43:
L65:
li $v0, 8
sw $v0, -4($fp)
addi $v0, $fp, -8
move $s0, $v0
lw $v0, -4($fp)
addi $v0, $v0, 1
move $a0, $v0
li $a1, 0
jal initArray
move $v1, $v0
lw $v0, -4($fp)
sw $v0, 0($v1) 
addi $v0, $v1, 4
move $v1, $v0
sw $v1, 0($s0) 
move $a0, $fp
jal L44
move $v0, $v0
j L64
L64:
jr $ra
