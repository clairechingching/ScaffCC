OPENQASM 2.0;
include "qelib1.inc";
qreg q[3];
creg cx0[1];
x q[0];
y q[0];
z q[0];
h q[0];
t q[0];
s q[0];
tdg q[0];
sdg q[0];
rx( 3.14159 ) q[0];
ry( 3.14159 ) q[0];
rz( 3.14159 ) q[0];
reset q[0];
h q[0];
reset q[0];
h q[0];
measure q[0] -> cx0[0];
measure q[0] -> cx0[0];
cx q[0], q[1];
ccx q[0], q[1], q[2];
//Decompose Fredkin(q0, q1, q2) = (I ⊗ CNOT(q1, q2)) * Toffoli(q0, q2, q1) * (I ⊗ CNOT(q1, q2))
cx q[1], q[2];
ccx q[0], q[1], q[2];
cx q[1], q[2];

