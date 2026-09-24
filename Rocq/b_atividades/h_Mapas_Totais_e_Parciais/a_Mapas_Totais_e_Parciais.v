(* MAPAS *)
(* MAPAS TOTAIS E PARCIAIS *)

(* Mapas (ou dicionários) são estruturas de dados onipresentes tanto na programação 
comum quanto na teoria de linguagens de programação; vamos precisar deles em vários 
lugares nos próximos capítulos.

Eles também servem como um ótimo estudo de caso usando ideias que vimos em capítulos 
anteriores, incluindo a construção de estruturas de dados a partir de funções de alta 
ordem (de Básico e Polimorfismo) e o uso de reflexão para otimizar provas (de IndProp).

Definiremos dois tipos de mapas: mapas totais, que incluem um elemento ''padrão'' a ser 
retornado quando a chave buscada não existe, e mapas parciais, que em vez disso 
retornam uma opção para indicar sucesso ou falha. Os mapas parciais são definidos em 
termos de mapas totais, usando None como o elemento padrão. *)