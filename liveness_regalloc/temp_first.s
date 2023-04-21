L12: .asciiz "\n"
L11:
L14:
la t135, L12
move t104, t135
jal L0
move t102, t102
j L13
L13:
last assem
jr $ra
L10:
L16:
li t132, 8
addi t136, t132, 1
move t104, t136
li t105, 0
jal initArray
move t133, t102
sw t132, 0(t133)
addi t137, t133, 4
move t133, t137
move t134, t133
move t104, t130
jal L11
move t102, t102
j L15
L15:
last assem
jr $ra
