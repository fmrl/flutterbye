-- $legal:629:
--
-- Copyright 2016 Michael Lowell Roberts & Microsoft Research
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.
--
--,$

-- adapted from the textadept F# lexer.

local l = require('lexer')
local token, word_match = l.token, l.word_match
local P, R, S = lpeg.P, lpeg.R, lpeg.S

local M = {_NAME = 'fstar'}

-- Whitespace.
local ws = token(l.WHITESPACE, l.space^1)

-- Comments.
local line_comment = P('//') * l.nonnewline^0
local block_comment = l.nested_pair('(*', '*)')
local comment = token(l.COMMENT, line_comment + block_comment)

-- Strings.
--local sq_str = l.delimited_range("'", true)
local dq_str = l.delimited_range('"', true)
--local string = token(l.STRING, sq_str + dq_str)
local string = token(l.STRING, dq_str)

-- Numbers.
local number = token(l.NUMBER, (l.float + l.integer * S('uUlL')^-1))

-- Preprocessor.
--[[
local preproc_word = word_match{
  'ifndef', 'ifdef', 'if', 'else', 'endif', 'light', 'region', 'endregion'
}
local preproc = token(l.PREPROCESSOR,
                      l.starts_line('#') * S('\t ')^0 * preproc_word *
                      (l.nonnewline_esc^1 + l.space * l.nonnewline_esc^0))
]]

-- Keywords.
local keyword = token(l.KEYWORD, word_match{
   'module', 'open',
   'type', 'and',
   'true', 'false',
   'Lemma', 'ensures', 'requires', 'decreases',
   'forall', 'exists',
   'val', 'let', 'rec', 'in',
   'abstract', 'inline', 'irreducible', 'private', 'unfoldable',
   'fun', 'function',
   'match', 'with',
   'if', 'then', 'else',
   'true', 'false', 'or', 'not',
   'assert', 'admit'
})

-- Types.
local type = token(l.TYPE, word_match{
  'Type',
  'True', 'False',
  'Tot', 'ML',
  'bool', 'int', 'nat', 'unit'
})

-- Identifiers.
local identifier = token(l.IDENTIFIER, l.word)

-- Operators.
local operator = token(l.OPERATOR, S('=<>+-*/\\^.,:;~!@#%^&|?[](){}'))

M._rules = {
  {'whitespace', ws},
  {'keyword', keyword},
  {'type', type},
  {'identifier', identifier},
  {'string', string},
  {'comment', comment},
  {'number', number},
  {'operator', operator},
}

return M
