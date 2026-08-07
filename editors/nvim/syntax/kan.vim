" Vim syntax file for the Kan programming language
" Language: Kan (.kan)
" See lib/tt.ml for the lexical grammar this mirrors.

if exists("b:current_syntax")
  finish
endif

" Comments: `--` to end of line (no block comments)
syn match   kanComment  "--.*$" contains=@Spell

" Strings: "..." with no escape sequences
syn region  kanString   start=+"+ end=+"+ oneline

" Numbers: Nat (123) and Integer (123z)
syn match   kanNumber   "\<\d\+z\?\>"

" Structural keywords
syn keyword kanKeyword  def data eval import match lambda

" Built-in base types; universes U, U1, U2, ... matched separately
syn keyword kanType     Type Nat Integer String Bool
syn match   kanType     "\<U\d*\>"

" A capitalized identifier is heuristically a type / type constructor
syn match   kanTypeName "\<\u\w*\>"

" Built-in constants and eliminators
syn keyword kanConstant zero suc refl true false
syn keyword kanBuiltin  natElim fst snd

" `def NAME` / `data NAME` — highlight the declared name
syn match   kanFunction "\%(\<def\s\+\)\@<=\<\h\w*"
syn match   kanTypeName "\%(\<data\s\+\)\@<=\<\h\w*"

" A constructor: identifier right after a match/data bar `|`
syn match   kanConstructor "\%(|\s*\)\@<=\<\h\w*"

" Operators
syn match   kanOperator "->\|=>\|λ\|[\\:=*.,|]"

" Highlight links — map to standard groups so colorschemes style them
hi def link kanComment      Comment
hi def link kanString       String
hi def link kanNumber       Number
hi def link kanKeyword      Keyword
hi def link kanType         Type
hi def link kanTypeName     Type
hi def link kanConstant     Constant
hi def link kanBuiltin      Function
hi def link kanFunction     Function
hi def link kanConstructor  Identifier
hi def link kanOperator     Operator

let b:current_syntax = "kan"
