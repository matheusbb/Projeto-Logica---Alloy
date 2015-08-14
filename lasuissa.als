module lasuissa

open util/ordering[Time]
-------------------------- ASSINATURAS --------------------------
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

-------------------------- FATOS --------------------------

fact Cliente{
	/*
	* Todo cliente esta na lanchonete e tem no maximo um pedido	
	*/
	all cliente: Cliente | cliente in Lanchonete.clientes
	all cliente: Cliente, t: Time-first | #(cliente.pedidos).t <= 1
}

fact Pedido{
	// Toda comida esta em um pedido
	all comida: Comida, t: Time-first | comida in (Pedido.comidas).t
	// Toda bebida esta em um pedido
	all bebida: Bebida, t: Time-first | bebida in (Pedido.bebidas).t
	//  Todo pedido esta ligado a algum cliente
	all p: Pedido, t: Time-first | (some c: Cliente | p in (c.pedidos).t)
	// Todo pedido tem alguma comida ou bebida
	all p : Pedido, t: Time-first | (some (p.bebidas).t) or (some (p.comidas).t)
	// Verifica se eh pacote um  
	all p1 : PacoteUm, t: Time-first | isPacoteUm[p1,t]
	// Verifica se eh pacote dois
	all p2 : PacoteDois, t: Time-first | isPacoteDois[p2,t]

}

fact Estoque {
	/*
	* Definição da quantidade de alimentos da lanchonete
	*/
	#Salgado <= 14
	#Sanduiche <= 14
	#Bebida <= 10
	#Sobremesa <= 7
}

fact traces {
	/*
	* Mudança do comportamento do modelo com o tempo
	*/
	init[first]
	all pre: Time-last| let pos = pre.next|
 	some  c: Cliente, p: Pedido, c1: Comida, b:Bebida, s: Sobremesa,t:Torta|
	addPedidoCliente[c,p, pre, pos] and
	addComidaPedido[p,c1,pre,pos] and 
	addBebidaPedido[p,b,pre,pos] and
	addSobremesaPacoteUm[p,s,pre,pos] and
   	addSobremesaPacoteDois[p,t,pre,pos]
}

-------------------------- FUNÇÕES --------------------------

fun getSalgados[p: Pedido, t: Time] : set Comida {
 	((p.comidas).t & (Coxinha + Pastel + Empada))
}

fun getSanduiche[p: Pedido, t: Time] : set Comida {
 	((p.comidas).t & (SanduicheAtum + SanduicheFrango))
}

fun getSobremesas[p: Pedido, t: Time] : set Comida {
 	((p.comidas).t & (Pudim + Torta + Brigadeiro))
}

fun getSucos[p: Pedido, t: Time] : set Suco {
 	((p.bebidas).t & Suco)
}

fun getRefrigerantes[p: Pedido, t: Time] : set Refrigerante {
 	((p.bebidas).t & Refrigerante)
}

-------------------------- PREDICADOS --------------------------

pred init[t: Time]{
	/*
	* Define o estado inicial do modelo
	* Clientes nao tem pedidos e pedido nao tem comida nem bebida
	*/
	all c: Cliente | no (c.pedidos).t
	all p: Pedido  | no (p.comidas).t and no (p.bebidas).t
}

pred isPacoteUm[p1:PacoteUm, t: Time]{
	/*
	* Verifica se o pedido atende as especificaçoes do pacote um
	*/
	(#(getSalgados[p1,t]) > 1 or #(getSanduiche[p1,t]) > 1)
 	and (some getSucos[p1,t] or some getRefrigerantes[p1,t])
}

pred isPacoteDois[p2: PacoteDois, t:Time]{
	/*
	* Verifica se o pedido atende as especificaçoes do pacote dois
	*/	
	(#(getSalgados[p2,t]) > 1 and (some getSanduiche[p2,t])) 
 	or (#(getSanduiche[p2,t]) > 1 and (some getSalgados[p2,t]))
  	and (#(getRefrigerantes[p2,t]) >= 1)
}

pred addPedidoCliente[c: Cliente, p: Pedido, antes , depois: Time]{
	/*
	* Adiciona pedido ao cliente caso ele nao o tenha
	*/
	(p !in (c.pedidos).antes)
	(c.pedidos).depois = (c.pedidos).antes + p 
}

pred addComidaPedido[p: Pedido, c: Comida, antes, depois: Time]{
	/*
	* Adiciona comida ao pedido
	*/
	c !in (p.comidas).antes
	(p.comidas).depois = (p.comidas).antes + c 
}

pred addBebidaPedido[p: Pedido, b: Bebida , antes, depois: Time]{
	/*
	* Adiciona bebida ao pedido
	*/
	(b !in (p.bebidas).antes)
	(p.bebidas).depois = (p.bebidas).antes + b
}

pred addSobremesaPacoteUm[p: Pedido , s: Sobremesa-Torta, antes, depois: Time ]{
	/*
	* Adiciona pudim ou brigadeiro
	*/
	(s !in (p.comidas).antes)
	(p.comidas).depois = (p.comidas).antes + s
}
pred addSobremesaPacoteDois[p: Pedido , t: Torta, antes, depois: Time ]{
	/*
	* Adiciona torta ao pedido
	*/
	(t !in (p.comidas).antes) 
	(p.comidas).depois = (p.comidas).antes + t
}

-------------------------- ASSERT'S --------------------------

assert pedidoTemBebidaOuComida{
	/*
	* Procura um pedido que nao tenha nem comida nem bebida
	*/
	!some p: Pedido | no p.bebidas and no p.comidas 
}

assert pacoteUm{
	/*
	* Procura um pacote um que nao atende as especificaçao do pacote
	*/
	!some p: PacoteUm, t: Time-first | no getSucos[p,t] and no getRefrigerantes[p,t] and 
	#(getSalgados[p,t]) < 2 and #(getSanduiche[p,t]) < 2 and #(getSobremesas[p,t]) < 2
}

assert pacoteDois{
	/*
	* Procura um pacote dois que nao atende as especificaçao do pacote
	*/
	!some p: PacoteDois, t: Time-first | no getRefrigerantes[p,t]
}

assert noPedidoSemCliente {
	/*
	* Procura se exite pedido sem cliente
	*/
	!some p: Pedido| all t: Time-first | (all c: Cliente | p !in (c.pedidos).t) 
}

-------------------------- CHECK'S --------------------------

--check noPedidoSemCliente for 20

--check pacoteDois for 30

--check pacoteUm for 20

--check pedidoTemBebidaOuComida for 20

pred show[]{}
run show for 7 but exactly 7 Cliente
