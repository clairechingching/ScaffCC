OPENQASM 2.0;
include "qelib1.inc";
qreg qb[4];
creg cbx0[1];
creg cbx1[1];
reset qb[0];
reset qb[1];
x qb[1];
reset qb[2];
h qb[2];
reset qb[3];
x qb[3];
h qb[3];
//Decompose Fredkin(q0, q1, q2) = (I ⊗ CNOT(q1, q2)) * Toffoli(q0, q2, q1) * (I ⊗ CNOT(q1, q2))
cx qb[1], qb[2];
ccx qb[0], qb[1], qb[2];
cx qb[1], qb[2];
h qb[2];
measure qb[2] -> cbx0[0];
measure qb[3] -> cbx1[0];

