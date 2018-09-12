type team = Korea | France | Usa | Brazil | Japan | Nigeria | Cameroon | Poland | Portugal | Italy | Germany |			Norway | Sweden | England | Argentina

type tourna = LEAF of team | NODE of tourna * tourna

let teamName : team -> string = fun(t) ->
	match t with
	| Korea -> "Korea"
	| France -> "France"
	| Usa -> "Usa"
	| Brazil -> "Brazil"
	| Japan -> "Japan"
	| Nigeria -> "Nigeria"
	| Cameroon -> "Cameroon"
	| Poland -> "Poland"
	| Portugal -> "Portugal"
	| Italy -> "Italy"
	| Germany -> "Germany"
	| Norway -> "Norway"
	| Sweden -> "Sweden"
	| England -> "England"
	| Argentina -> "Argentina"

let rec parenize : tourna -> string = fun(tor) ->
	match tor with
	| LEAF t -> teamName(t)
	| NODE (tor1,tor2) -> "(" ^ parenize(tor1) ^ " " ^ parenize(tor2) ^ ")"
