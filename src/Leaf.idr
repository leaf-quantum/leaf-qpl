module Leaf

-- a module used to load Leaf libraries in REPL sessions

import Frontend.ASTData
import Frontend.ASTPhases
import Compiler.Validation.PostParseValidation
import Frontend.Source
import Frontend.Token
import Compiler.Type
import Frontend.Lexer.Error
import Frontend.Lexer.Lexer
import Frontend.Lexer.Regex
import Frontend.Lexer.Rules
import Frontend.Parser.Error
import Frontend.Parser.Helper
import Frontend.Parser.Parser
import Frontend.Syntax.AST
import Frontend.Utils.ASTDebugPrinter
import Frontend.Utils.ASTPrettyPrinter
import Frontend.Syntax.Attribute
import Frontend.Syntax.Common
import Frontend.Syntax.Contract
import Frontend.Syntax.Doc
import Frontend.Syntax.Literal
import Frontend.Syntax.Name
import Frontend.Syntax.Operator
import Frontend.Syntax.Pattern
import Frontend.Syntax.Type
import Compiler.Desugar.Desugar
import Compiler.Desugar.Helper
import Compiler.ScopeAndNameResolution.Resolve
import Compiler.TypeChecker.InitialTypeCheckPass