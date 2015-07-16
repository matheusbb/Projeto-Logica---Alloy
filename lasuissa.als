module lasuissa

sig Comida{
}

sig Bebida{
}

sig Pedido{
	 comidas : set Comida,
	 bebidas : set Bebida
}

sig Salgado extends Comida{
}

sig Sanduiche extends Comida{
}

sig Sobremesa extends Comida {
}

sig PedidoConvencional extends Pedido{
}

sig Pacote extends Pedido {
}

pred show[]{}
run show 


