// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
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
"equals"              return 'EQUALS'
"as"                  return 'AS'
"typedef"             return 'TYPEDEF'
"none"                return 'NONE'
"top"                 return 'TOP'
"not"                 return 'NOT'
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
"=="                  return '=='
"="                   return '='
"!"                   return '!'
"["                   return '['
"]"                   return ']'
"{"                   return '{'
"}"                   return '}'
"/"                   return '/'
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

file : 
	EOF { return AST.makeProgram(null,null,[],@$); }
  | program EOF { return $1; }
  ;

// TYPES

type_root :
	  type_rg
	| FORALL IDENTIFIER '.' type_root
		{ $$ = AST.makeForallType($2,$4,null,@$); }
	| FORALL IDENTIFIER '<:' type_root '.' type_root
		{ $$ = AST.makeForallType($2,$6,$4,@$); }
	| EXISTS IDENTIFIER '.' type_root
		{ $$ = AST.makeExistsType($2,$4,null,@$); }
	| EXISTS IDENTIFIER '<:' type_root '.' type_root
		{ $$ = AST.makeExistsType($2,$6,$4,@$); }
	| alternative_type // groups all alternatives, easier commutative ops.
		{ $$ = AST.makeAlternativeType($1,@$); }
	| intersection_type // same.
		{ $$ = AST.makeIntersectionType($1,@$); }
	| type_rg '{' type_root '/' id '}'
		{ $$ = AST.makeSubstitution($1,$3,$5,@$); }
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

id :
	IDENTIFIER
	 	{ $$ = AST.makeNameType(yytext,@$); }
	;

type :
	 '!' type
 	  	{ $$ = AST.makeBangType($2,@$); }
	| id
	 	{ $$ = $1; }
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
	| NONE
		{ $$ = AST.makeNoneType(@$); }
	| TOP
		{ $$ = AST.makeTopType(@$); }
	// Primitive Types
	| INT_TYPE
	 	{ $$ = AST.makePrimitiveType(yytext,@$); }
	| BOOLEAN_TYPE
	 	{ $$ = AST.makePrimitiveType(yytext,@$); }
	| STRING_TYPE
	 	{ $$ = AST.makePrimitiveType(yytext,@$); }
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

ids_list :
	IDENTIFIER
		{ $$ = [$1]; }
	| IDENTIFIER ',' ids_list
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
	  TYPEDEF IDENTIFIER "=" type_root
		{ $$ = AST.makeTypedef($2,$4,null,@$); }
	| TYPEDEF IDENTIFIER typedef_pars "=" type_root
		{ $$ = AST.makeTypedef($2,$5,$3,@$); }
	;

typedef_pars :
	'<' ids_list '>'
		{ $$ = $2; }
	;

sequence :
	  forall
	| forall sequence
	 { $$ = $1.concat($2); }
	;

forall :
      '<' IDENTIFIER '>' forall
		{ $$ = [AST.makeForall($2,$4[0],@$)]; }
    | share
		{ $$ = $1; }
	| subtype
		{ $$ = $1; }
	| equals
		{ $$ = $1; }
	;

share :
	SHARE type_root AS type_root '||' type_root
	 { $$ = [AST.makeShare(true,$2,$4,$6,@$)]; }
	| NOT SHARE type_root AS type_root '||' type_root
	 { $$ = [AST.makeShare(false,$3,$5,$7,@$)]; }
	;

subtype :
	SUBTYPE type_root '<:' type_root
	 { $$ = [AST.makeSubtype(true,$2,$4,@$)]; }
	| NOT SUBTYPE type_root '<:' type_root
	 { $$ = [AST.makeSubtype(false,$3,$5,@$)]; }
	;

equals :
	EQUALS type_root '==' type_root
	 { $$ = [AST.makeEquals(true,$2,$4,@$)]; }
	| NOT EQUALS type_root '==' type_root
	 { $$ = [AST.makeEquals(false,$3,$5,@$)]; }
	;

