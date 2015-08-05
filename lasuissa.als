module lasuissa

open util/ordering[Time] as to

sig Time {}

one sig Lanchonete {
	clientes : set Cliente -> Time
}
sig Cliente {
	--pedidos : one Pedido -> Time
	-- Porque com o one nao funciona
	--Erro : After the some/lone/one multiplicity symbol, this expression
	--must be a unary set.
	--Instead, its possible type(s) are:
	--{this/Pedido->this/Time}
	pedidos : Pedido -> Time
}

abstract sig Comida{}
abstract sig Bebida{}
abstract sig Pedido{
	 comidas : set Comida  ->Time,
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
	--all cliente: Cliente, t: Time | some cliente.pedidos and cliente in (Lanchonete.clientes).t
	--all pedido: Pedido, t: Time | pedido in (Cliente.pedidos).t
	-- E falso porque no tempo 0 nao temos clientes com pedidos, nem lanchonete com cliente
}

fact Pedido{
	--all comida: Comida, t: Time | comida in (Pedido.comidas).t
	--all bebida: Bebida, t: Time  | bebida in (Pedido.bebidas).t
	-- E falso porque no tempo 0 nao tem comida nem bebida no pedido
	
	all p : Pedido | (some p.bebidas) or (some p.comidas)

	all p1 : PacoteUm , t: Time | (#(numSalgados[p1,t]) > 1 or #(numSanduiche[p1,t]) > 1 or #(numSobremesas[p1,t]) > 1)
 	and (some sucos[p1,t] or some refrigerantes[p1,t])

	all p2 : PacoteDois, t: Time | (#(numSalgados[p2,t]) > 1 and (some numSanduiche[p2,t] or some numSobremesas[p2,t])) 
 	or (#(numSanduiche[p2,t]) > 1 and (some numSalgados[p2,t] or some numSobremesas[p2,t]))
 	or (#(numSobremesas[p2,t]) > 1 and (some numSalgados[p2,t] or some numSanduiche[p2,t]))
 	and (some refrigerantes[p2,t])
}

fact Estoque { 
	#Salgado <= 14
 	--all lanchonete:Lanchonete,  coxinha:Coxinha, pastel:Pastel, empada:Empada |
 	--#((((lanchonete.clientes).pedidos).comidas) & (coxinha + pastel + empada)) = 14
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
 	((p.bebidas).t  & Suco)
}

fun refrigerantes[p: Pedido, t: Time] : set Refrigerante {
 	((p.bebidas).t & Refrigerante)
}

fact traces {
	init[first]
	all pre: Time-last| let pos = pre.next |
 	all l: Lanchonete , p: Pedido , c: Cliente|
	addClienteNaLanchonete[l,c,pre,pos] and
	addPedidoDoCliente[c,p, pre, pos]

}

pred init[t: Time]{
	no (Cliente.pedidos).t and
	no (Lanchonete.clientes).t and
	no (Pedido.comidas).t and
	no (Pedido.bebidas).t
}

pred addClienteNaLanchonete[l: Lanchonete, c: Cliente, t, t': Time]{
	c !in (l.clientes).t
	(l.clientes).t' = (l.clientes).t + c 
}

pred addPedidoDoCliente[c: Cliente, p: Pedido, t, t': Time]{
	p !in (c.pedidos).t 
	(c.pedidos).t' = (c.pedidos).t + p
}

assert pedidoTemBebidaOuComida{
	!some p: Pedido | no p.bebidas and no p.comidas 
}

assert pacoteUm{
	!some p: PacoteUm, t: Time | no sucos[p,t] and no refrigerantes[p,t] and 
	#(numSalgados[p,t]) < 2 and #(numSanduiche[p,t]) < 2 and #(numSobremesas[p,t]) < 2

}

assert pacoteDois{
	!some p:PacoteDois,t: Time | no refrigerantes[p,t]

}

--check pacoteDois for 70

--check pacoteUm for 70

--check pedidoTemBebidaOuComida for 100

pred show[]{}

run show for 7 but exactly 7 Cliente
