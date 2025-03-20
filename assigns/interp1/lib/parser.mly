%{
open Utils
%}

%token EOF

%start <Utils.prog> prog

%%

prog:
  | EOF { Unit }
