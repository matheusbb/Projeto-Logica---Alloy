module lasuissa

open util/ordering[Time]

sig Time {}

one sig Lanchonete {
	clientes : set Cliente
}
sig Cliente {
	pedidos : one Pedido
}

abstract sig Comida{}
abstract sig Bebida{}
abstract sig Pedido{
	 comidas : set Comida,
	 bebidas : set Bebida
}

abstract sig Salgado extends Comida{}
abstract sig Sanduiche extends Comida{}
abstract sig Sobremesa extends Comida {}

sig Agua extends Bebida{}
sig Refrigerante extends Bebida{}
sig Suco extends Bebida{}

sig Coxinha extends Salgado{}
sig Empada extends Salgado{}
sig Pastel extends Salgado{}

sig SanduicheFrango extends Sanduiche{}
sig SanduicheAtum extends Sanduiche{}

sig Pudim extends Sobremesa{}
sig Torta extends Sobremesa{}
sig Brigadeiro extends Sobremesa{}

sig PedidoConvencional extends Pedido{}
sig PacoteUm extends Pedido {}
sig PacoteDois extends Pedido {}

fact Cliente{
	all cliente: Cliente| some cliente.pedidos and cliente in Lanchonete.clientes
	all pedido: Pedido| pedido in Cliente.pedidos
}

fact Pedido{
	all comida: Comida| comida in Pedido.comidas
	all bebida: Bebida| bebida in Pedido.bebidas
	
	all p : Pedido | (some p.bebidas) or (some p.comidas)

	all p1 : PacoteUm | (#(numSalgados[p1]) > 1 or #(numSanduiche[p1]) > 1 or #(numSobremesas[p1]) > 1)
 	and (some sucos[p1] or some refrigerantes[p1])

	all p2 : PacoteDois | (#(numSalgados[p2]) > 1 and (some numSanduiche[p2] or some numSobremesas[p2])) 
 	or (#(numSanduiche[p2]) > 1 and (some numSalgados[p2] or some numSobremesas[p2]))
 	or (#(numSobremesas[p2]) > 1 and (some numSalgados[p2] or some numSanduiche[p2]))
 	and (some refrigerantes[p2])
}

fact Estoque { 
	#Salgado <= 14
 	--all lanchonete:Lanchonete,  coxinha:Coxinha, pastel:Pastel, empada:Empada |
 	--#((((lanchonete.clientes).pedidos).comidas) & (coxinha + pastel + empada)) = 14
}

fun numSalgados[p: Pedido] : set Comida {
 	(p.comidas & (Coxinha + Pastel + Empada))
}

fun numSanduiche[p: Pedido] : set Comida {
 	(p.comidas & (SanduicheAtum + SanduicheFrango))
}

fun numSobremesas[p: Pedido] : set Comida {
 	(p.comidas & (Pudim + Torta + Brigadeiro))
}

fun sucos[p: Pedido] : set Suco {
 	(p.bebidas & Suco)
}

fun refrigerantes[p: Pedido] : set Refrigerante {
 	(p.bebidas & Refrigerante)
}

assert pedidoTemBebidaOuComida{
<<<<<<< HEAD
	!some p: Pedido | no p.bebidas and no p.comidas 
}

assert pacoteUm{
=======
	 -- all p: Pedido | #p.bebidas >= 1 or #p.comidas >= 1
!some p: Pedido | no p.bebidas and no p.comidas 
}

assert pacoteUM{
>>>>>>> 448c54adcec8c35e1e1b544f13171e3fae717cf7
	!some p: PacoteUm | no sucos[p] and no refrigerantes[p] and 
	#(numSalgados[p]) < 2 and #(numSanduiche[p]) < 2 and #(numSobremesas[p]) < 2

}

<<<<<<< HEAD
assert pacoteDois{
=======
assert pacoteDOIS{
>>>>>>> 448c54adcec8c35e1e1b544f13171e3fae717cf7
	!some p:PacoteDois | no refrigerantes[p]

}

<<<<<<< HEAD
check pacoteDois for 70

check pacoteUm for 70
=======
check pacoteDOIS for 70

check pacoteUM for 70
>>>>>>> 448c54adcec8c35e1e1b544f13171e3fae717cf7

check pedidoTemBebidaOuComida for 100

pred show[]{}
run show for 7 but exactly 7 Cliente

