// Copyright (C) 2013-2014 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/* lexical grammar */
%lex

%%

\s+                   /* skip whitespace */
\/\/.*                /* skip comments */
"/*"(.|\n|\r)*?"*/"   /* skip multiline comment */
"int"                 return 'INT_TYPE'
"boolean"             return 'BOOLEAN_TYPE'
"string"              return 'STRING_TYPE'
"share"               return 'SHARE'
"subtype"             return 'SUBTYPE'
"as"                  return 'AS'
"typedef"             return 'TYPEDEF'
"none"                return 'NONE'
"(+)"                 return '(+)'
"&"                   return '&'
"||"                  return '||'
"#"                   return '#'
"("                   return '('
")"                   return ')'
"<:"                  return '<:'
"<"                   return '<'
">"                   return '>'
"+"                   return '+'
"*"                   return '*'
"."                   return '.'
","                   return ','
";"                   return ';'
"::"                  return '::'
":"                   return ':'
"=>"                  return '=>'
"="                   return '='
"!"                   return '!'
"["                   return '['
"]"                   return ']'
"-o"                  return '-o'
"rw"                  return 'RW'
"ref"                 return 'REF'
"exists"              return 'EXISTS'
"forall"              return 'FORALL'
[a-zA-Z0-9_]+         return 'IDENTIFIER'
<<EOF>>               return 'EOF'
/lex

%start file

%% /* language grammar */

file : program EOF { return $1; };

// TYPES

type_root :
	  type_rg
	| FORALL IDENTIFIER '.' type_root
		{ $$ = AST.makeForallType($2,$4,@$); }
	| EXISTS IDENTIFIER '.' type_root
		{ $$ = AST.makeExistsType($2,$4,@$); }
	| alternative_type // groups all alternatives, easier commutative ops.
		{ $$ = AST.makeAlternativeType($1,@$); }
	| intersection_type // same.
		{ $$ = AST.makeIntersectionType($1,@$); }
	;

type_rg :
	  type_fun
	| type_fun '=>' type_rg
		{ $$ = AST.makeRelyType($1,$3,@$); }
	| type_fun ';' type_rg
		{ $$ = AST.makeGuaranteeType($1,$3,@$); }
	;

type_fun :
	  type_cap
	| type_fun '-o' type_cap
		{ $$ = AST.makeFunType($1,$3,@$); }
	| IDENTIFIER '[' type_list ']'
		{ $$ = AST.makeDefinitionType($1,$3,@$); }
	;

type_cap :
	  type
	| type_cap '::' type
		{ $$ = AST.makeStackedType($1,$3,@$); }
	| type '*' star_type
		{ $$ = AST.makeStarType([$1].concat($3),@$); }
	| sum_type
		{ $$ = AST.makeSumType($1,@$); }
	;
	

type :
	 '!' type
 	  	{ $$ = AST.makeBangType($2,@$); }
	| IDENTIFIER
	 	{ $$ = AST.makeNameType(yytext,@$); }
	| REF IDENTIFIER
	 	{ $$ = AST.makeRefType($2,@$); }
	| '(' type_root ')'
	 	{ $$ = $2; }
	| RW IDENTIFIER type
		{ $$ = AST.makeCapabilityType($2,$3,@$); }
	| '[' ']'
	 	{ $$ = AST.makeRecordType([],@$); }
	| '[' field_types ']'
	 	{ $$ = AST.makeRecordType($2,@$); }
	| '[' type_list ']'
		{ $$ = AST.makeTupleType($2,@$); }
	// Primitive Types
	| INT_TYPE
	 	{ $$ = AST.makePrimitiveType(yytext,@$); }
	| BOOLEAN_TYPE
	 	{ $$ = AST.makePrimitiveType(yytext,@$); }
	| NONE
		{ $$ = AST.makeNoneType(@$); }
	;

tagged :
	IDENTIFIER '#' type
	 	{ $$ = AST.makeTaggedType($1,$3,@$); }
	;

intersection_type :
	  type_fun '&' type_fun
	  	{ $$ = [$1,$3]; }
	| intersection_type '&' type_fun
		{ $$ = $1.concat([$3]); }
	;

alternative_type :
	  type_fun '(+)' type_fun
	  	{ $$ = [$1,$3]; }
	| alternative_type '(+)' type_fun
		{ $$ = $1.concat([$3]); }
	;
	
star_type :
	  type
	  	{ $$ = [$1]; }
	| type '*' star_type
		{ $$ = [$1].concat($3); }
	;

sum_type :
	tagged
		{ $$ = [$1]; }
	| tagged '+' sum_type
		{ $$ = [$1].concat($3); }
	;

type_list :
	type_root
		{ $$ = [$1]; }
	| type_root ',' type_list
		{ $$ = [$1].concat($3); }
	;

field_type :
	IDENTIFIER ':' type_root
		{ $$ = AST.makeFieldType($1,$3,@$); }
	;
	
field_types :
	  field_type
		{ $$ = [$1]; }
	| field_type ',' field_types
		{ $$ = [$1].concat($3); }
	;

// EXPRESSIONS

program :
	  sequence
	  	{ $$ = AST.makeProgram(null,null,$1,@$); }
	| typedefs sequence
		{ $$ = AST.makeProgram(null,$1,$2,@$); }
	;

typedefs :
	typedef
		{ $$ = [$1]; }
	| typedef typedefs
		{ $$ = [$1].concat($2); }
	;

typedef :
	  TYPEDEF IDENTIFIER "=" type
		{ $$ = AST.makeTypedef($2,$4,null,@$); }
	| TYPEDEF IDENTIFIER typedef_pars "=" type
		{ $$ = AST.makeTypedef($2,$5,$3,@$); }
	;

typedef_pars :
	'<' ids_list '>'
		{ $$ = $2; }
	;

sequence :
	  share
	| subtype
	| share sequence
	| subtype sequence
	;

share :
	SHARE type_root AS type_root '||' type_root
	 { $$ = AST.makeShare($2,$4,$6,@$); }
	;

subtype :
	SUBTYPE type_root '<:' type_root
	 { $$ = AST.makeSubtype($2,$4,@$); }
	;

ids_list :
	IDENTIFIER
		{ $$ = [$1]; }
	| IDENTIFIER ',' ids_list
		{ $$ = [$1].concat($3); }
	;


// ========================

/*
sequence :
	sharing
	| sharing ';' sequence
		{ $$ = AST.makeLet(null,$1,$3,@$); }
	;

sharing_type_list :
	type
		{ $$ = [$1]; }
	| type ',' sharing_type_list
		{ $$ = [$1].concat($3); }
	;

nonsequence :
	expression
	| nonsequence "." IDENTIFIER
		{ $$ = AST.makeSelect($1,$3,@$); }
	| nonsequence ":=" expression
		{ $$ = AST.makeAssign($1,$3,@$); }
	| nonsequence expression
		{ $$ = AST.makeCall($1,$2,@$); }
	| nonsequence '[' type_root ']'
		{ $$ = AST.makeTypeApp($1,$3,@$); }
	| nonsequence '::' type
		{ $$ = AST.makeCapStack($1,$3,@$); }
	;

expression :
	  value
	| "!" expression
		{ $$ = AST.makeDeRef($2,@$); }
	| NEW expression
		{ $$ = AST.makeNew($2,@$); }
	| '<' IDENTIFIER '>' expression
		{ $$ = AST.makeForall($2,$4,@$); }
	| '<' type_root ',' sequence '>'
		{ $$ = AST.makePack($2,null,$4,@$); }
	| '<' type_root ':' IDENTIFIER ',' sequence '>'
		{ $$ = AST.makePack($2,$4,$6,@$); }
	| DELETE expression
		{ $$ = AST.makeDelete($2,@$); }
	| USE type_root IN sequence END
		{ $$ = AST.makeUse($2,$4,@$); }
	| LET IDENTIFIER '=' sequence IN sequence END
		{ $$ = AST.makeLet($2,$4,$6,@$); }
	| LET '[' ids_list ']' '=' sequence IN sequence END
		{ $$ = AST.makeLetTuple($3,$6,$8,@$); }
	| OPEN '<'IDENTIFIER ',' IDENTIFIER'>' '=' sequence IN sequence END
		{ $$ = AST.makeOpen($3,$5,$8,$10,@$); }
	| "(" sequence ")"
		{ $$ = $2; }
	| IDENTIFIER '#' expression
		{ $$ = AST.makeTagged($1,$3,@$); }
	| CASE nonsequence OF branches END
		{ $$ = AST.makeCase($2,$4,@$); }
	| '{' tuple '}'
		{ $$ = AST.makeTuple($2,@$); }
    ;

branches :
	  branch
	  	{ $$ = [$1]; }
	| branch '|' branches
		{ $$ = [$1].concat($3); }
	;

branch :
	IDENTIFIER '#' IDENTIFIER '->' sequence
		{ $$ = AST.makeBranch($1,$3,$5,@$); }
	;

tuple :
	nonsequence
		{ $$ = [$1]; }
	| nonsequence ',' tuple
		{ $$ = [$1].concat($3); }
	;

function :
	FUN IDENTIFIER '(' parameter ends_with_type
		{ $$ = AST.makeFunction( $2, $4, $5.exp, $5.result, null, @$ ); }
	| FUN IDENTIFIER quantification '(' parameter ends_with_type
		{ $$ = AST.makeFunction( $2, $5, $6.exp, $6.result, $3, @$ ); }
	| FUN '(' parameter ends_without_type
		{ $$ = AST.makeFunction( null, $3, $4.exp, $4.result, null, @$ ); }
	;

ends_with_type :
	')' ':' type_root '.' expression
		{ $$ = { result : $3, exp : $5 }; }
	| ',' parameter ends_with_type
		{ $$ = { result : AST.makeFunType($2.type,$3.result),
			exp : AST.makeFunction( null , $2, $3.exp, $3.result, null, @$ ) }; }
	;

ends_without_type :
	')' '.' expression
		{ $$ = { result : null, exp : $3 }; }
	| ',' parameter ends_without_type
		{ $$ = { result : AST.makeFunType($2.type,$3.result),
			exp : AST.makeFunction( null , $2, $3.exp, $3.result, null, @$ ) }; }
	;

quantification :
	  '<' IDENTIFIER '>'
	  	{ $$ = [$2]; }
	| '<' IDENTIFIER '>' quantification
		{ $$ = [$2].concat($4); }
	;
	
parameter : 
	IDENTIFIER  ':' type_root
		{ $$ = AST.makeParameters($1,$3,@$); }
	;


value :
      IDENTIFIER 
      	{ $$ = AST.makeID(yytext,@$); }
    | NUMBER
		{ $$ = AST.makeNumber(yytext,@$); }
    | BOOLEAN
		{ $$ = AST.makeBoolean(yytext,@$); }
    | STRING
		{ $$ = AST.makeString(yytext,@$); }
    | record
    | function
 	;
	
record :
	  '{' '}'
	  	{ $$ = AST.makeRecord([],@$); }
	| '{' fields '}'
		{ $$ = AST.makeRecord($2,@$); }
	;
	
field :
	IDENTIFIER '=' value
		{ $$ = AST.makeField($1,$3,@$); }
	;

fields :
	  field
	  	{ $$ = [$1]; }
	| field ',' fields
		{ $$ = [$1].concat($3); }
	;

	*/