module lasuissa

open util/ordering[Time]

sig Time {}

one sig Lanchonete {
	clientes : set Cliente
}

sig Cliente {
	pedidos : Pedido -> Time
}

abstract sig Comida{}
abstract sig Bebida{}
abstract sig Pedido{
	 comidas : set Comida -> Time,
	 bebidas : set Bebida -> Time
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
	all cliente: Cliente | cliente in Lanchonete.clientes
	all cliente: Cliente, t: Time-first | #(cliente.pedidos).t <= 1
	--all pedido: Pedido, t: Time | pedido in (Cliente.pedidos).t
}

fact Pedido{
	all comida: Comida, t: Time-first | comida in (Pedido.comidas).t
	all bebida: Bebida, t: Time-first | bebida in (Pedido.bebidas).t
	
	all p: Pedido, t: Time-first | (some c: Cliente | p in (c.pedidos).t)

	all p : Pedido, t: Time-first | (some (p.bebidas).t) or (some (p.comidas).t)

	all p1 : PacoteUm, t: Time| (#(numSalgados[p1,t]) > 1 or #(numSanduiche[p1,t]) > 1 or #(numSobremesas[p1,t]) > 1)
 	and (some sucos[p1,t] or some refrigerantes[p1,t])

	all p2 : PacoteDois, t: Time | (#(numSalgados[p2,t]) > 1 and (some numSanduiche[p2,t] or some numSobremesas[p2,t])) 
 	or (#(numSanduiche[p2,t]) > 1 and (some numSalgados[p2,t] or some numSobremesas[p2,t]))
 	or (#(numSobremesas[p2,t]) > 1 and (some numSalgados[p2,t] or some numSanduiche[p2,t]))
 	and (some refrigerantes[p2,t])
}

fact traces {
	init[first]
	all pre: Time-last| let pos = pre.next|
 	some  c: Cliente, p: Pedido, c1: Comida|
	addPedidoCliente[c,p, pre, pos] and
	addComidaPedido[p,c1,pre,pos]	
	
}

fun numSalgados[p: Pedido, t: Time] : set Comida {
 	((p.comidas).t & (Coxinha + Pastel + Empada))
}

fun numSanduiche[p: Pedido, t: Time] : set Comida {
 	((p.comidas).t & (SanduicheAtum + SanduicheFrango))
}

fun numSobremesas[p: Pedido, t: Time] : set Comida {
 	((p.comidas).t & (Pudim + Torta + Brigadeiro))
}

fun sucos[p: Pedido, t: Time] : set Suco {
 	((p.bebidas).t & Suco)
}

fun refrigerantes[p: Pedido, t: Time] : set Refrigerante {
 	((p.bebidas).t & Refrigerante)
}

assert pedidoTemBebidaOuComida{
	!some p: Pedido | no p.bebidas and no p.comidas 
}

assert pacoteUm{
	!some p: PacoteUm, t: Time| no sucos[p,t] and no refrigerantes[p,t] and 
	#(numSalgados[p,t]) < 2 and #(numSanduiche[p,t]) < 2 and #(numSobremesas[p,t]) < 2

}

assert pacoteDois{
	!some p:PacoteDois, t: Time | no refrigerantes[p,t]
}

assert noPedidoSemCliente {
	!some p: Pedido, t: Time | (all c: Cliente | p !in (c.pedidos).t) 
}

pred init[t: Time]{
	all c: Cliente | no (c.pedidos).t
	all p:Pedido  | no (p.comidas).t and no (p.bebidas).t
}

pred addPedidoCliente[ c:Cliente, p:Pedido, antes , depois: Time]{
	(p !in (c.pedidos).antes)
	(c.pedidos).depois = (c.pedidos).antes + p 
}

pred addComidaPedido[p:Pedido, c:Comida, antes, depois:Time]{
	c !in (p.comidas).antes
	(p.comidas).depois = (p.comidas).antes + c 
}

--check noPedidoSemCliente for 10

--check pacoteDois for 70

--check pacoteUm for 70

--check pedidoTemBebidaOuComida for 100

pred show[]{}
run show for 7 but exactly 7 Cliente
