module lasuissa

one sig Lanchonete {
	clientes : set Cliente
}
sig Cliente {
	pedidos : set Pedido
}

abstract sig Comida{}

abstract sig Bebida{}

abstract sig Pedido{
	 comidas : set Comida,
	 bebidas : set Bebida
}

abstract sig Salgado extends Comida{
}

abstract sig Sanduiche extends Comida{
}

abstract sig Sobremesa extends Comida {
}

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
	
	all p1 : PacoteUm | (#(numSalgados[p1]) > 1 or #(numSalgados[p1]) > 1)
 	and ((p1.bebidas in Suco) and (some p1.bebidas) 
 	or (p1.bebidas in Refrigerante) and (some p1.bebidas))
}

fact Estoque { 
	all lanchonete:Lanchonete,  coxinha:Coxinha, pastel:Pastel, empada:Empada |
 	#((((lanchonete.clientes).pedidos).comidas) & (coxinha + pastel + empada)) = 14
}

fun numSalgados[p: Pedido] : set Comida {
 	(p.comidas & (Coxinha + Pastel + Empada))
}

fun numSanduiche[p: Pedido] : set Comida {
 	(p.comidas & (SanduicheAtum + SanduicheFrango))
}

pred show[]{}
run show for 7 but exactly 7 Cliente
