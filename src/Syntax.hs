module Syntax where

import Text.ParserCombinators.Parsec
import Text.Parsec.Token
import Text.ParserCombinators.Parsec.Language
import Numeric

type S1Program = [S1Class]

type S1Class = (SourcePos, String, String, [S1Field], [S1Method])

type S1Method = (SourcePos, String, String, [(String, String)], S1Expr)

type S1Field = (SourcePos, String, String, S1Expr)

data S1Feature = FeatureMethod S1Method | FeatureField S1Field

data S1Expr = S1Void                                             |
              S1Self SourcePos                                   |
              S1True SourcePos                                   |
              S1False SourcePos                                  |
              S1String SourcePos String                          |
              S1Integer SourcePos Integer                        |
              S1Variable SourcePos String                        |
              S1Dot SourcePos S1Expr String String [S1Expr]      |
              S1New SourcePos String                             |
              S1UnaryOp SourcePos String S1Expr                  |
              S1BinaryOp SourcePos String S1Expr S1Expr          |
              S1Block SourcePos [S1Expr]                         |
              S1If SourcePos S1Expr S1Expr S1Expr                |
              S1While SourcePos S1Expr S1Expr                    |
              S1Let SourcePos [(String, String, S1Expr)] S1Expr  |
              S1Case SourcePos S1Expr [(String, String, S1Expr)] |
              S1Assign SourcePos String S1Expr

showsWithSep :: Show a => String -> [a] -> String -> String
showsWithSep _ [] = (++) ""
showsWithSep _ [x] = shows x
showsWithSep sep (x : xs) = shows x . (++) sep . showsWithSep sep xs

instance Eq S1Expr where
        S1Void == S1Void = True
        S1Self _ == S1Self _ = True
        S1True _ == S1True _ = True
        S1False _ == S1False _ = True
        S1String _ str1 == S1String _ str2 = str1 == str2
        S1Integer _ int1 == S1Integer _ int2 = int1 == int2
        S1Variable _ name1 == S1Variable _ name2 = name1 == name2
        S1Dot _ expr1 ctype1 name1 args1 == S1Dot _ expr2 ctype2 name2 args2 = expr1 == expr2 && ctype1 == ctype2 && name1 == name2 && args1 == args2
        S1New _ ctype1 == S1New _ ctype2 = ctype1 == ctype2
        S1UnaryOp _ op1 expr1 == S1UnaryOp _ op2 expr2 = op1 == op2 && expr1 == expr2
        S1BinaryOp _ op1 expr1 expr2 == S1BinaryOp _ op2 expr3 expr4 = op1 == op2 && expr1 == expr3 && expr2 == expr4
        S1Block _ exprs1 == S1Block _ exprs2 = exprs1 == exprs2
        S1If _ cond1 expr1 expr2 == S1If _ cond2 expr3 expr4 = cond1 == cond2 && expr1 == expr3 && expr2 == expr4
        S1While _ cond1 expr1 == S1While _ cond2 expr2 = cond1 == cond2 && expr1 == expr2
        S1Let _ vars1 expr1 == S1Let _ vars2 expr2 = vars1 == vars2 && expr1 == expr2
        S1Case _ expr1 variants1 == S1Case _ expr2 variants2 = expr1 == expr2 && variants1 == variants2
        S1Assign _ name1 expr1 == S1Assign _ name2 expr2 = name1 == name2 && expr1 == expr2
        _ == _ = False

instance Show S1Expr where
        showsPrec _ S1Void = showString "void"
        showsPrec _ (S1Self _) = showString "self"
        showsPrec _ (S1True _) = showString "true"
        showsPrec _ (S1False _) = showString "false"
        showsPrec _ (S1String _ str) = showChar '"' .
                                       showString str .
                                       showChar '"'
        showsPrec _ (S1Integer _ int) = showInt int
        showsPrec _ (S1Variable _ name) = showString name
        showsPrec _ (S1Dot _ expr "" name args) = showsPrec 7 expr .
                                                  showChar '.' .
                                                  showString name .
                                                  (showParen True $ showsWithSep ", " args)
        showsPrec _ (S1Dot _ expr ctype name args) = showsPrec 7 expr .
                                                     showChar '@' .
                                                     showString ctype .
                                                     showChar '.' .
                                                     showString name .
                                                     (showParen True $ showsWithSep ", " args)
        showsPrec _ (S1New _ ctype) = showString "new " .
                                      showString ctype
        showsPrec d (S1UnaryOp _ "not" expr) = showParen (d > 1) $
                                               showString "not " .
                                               showsPrec 1 expr
        showsPrec d (S1UnaryOp _ "isvoid" expr) = showParen (d > 5) $
                                                  showString "isvoid " .
                                                  showsPrec 5 expr
        showsPrec d (S1UnaryOp _ "~" expr) = showParen (d > 6) $
                                             showString "~" .
                                             showsPrec 6 expr
        showsPrec d (S1BinaryOp _ "<=" expr1 expr2) = showParen (d > 2) $
                                                      showsPrec 2 expr1 .
                                                      showString "<=" .
                                                      showsPrec 2 expr2
        showsPrec d (S1BinaryOp _ "<" expr1 expr2) = showParen (d > 2) $
                                                     showsPrec 2 expr1 .
                                                     showChar '<' .
                                                     showsPrec 2 expr2
        showsPrec d (S1BinaryOp _ "=" expr1 expr2) = showParen (d > 2) $
                                                     showsPrec 2 expr1 .
                                                     showChar '=' .
                                                     showsPrec 2 expr2
        showsPrec d (S1BinaryOp _ "+" expr1 expr2) = showParen (d > 3) $
                                                     showsPrec 3 expr1 .
                                                     showChar '+' .
                                                     showsPrec 3 expr2
        showsPrec d (S1BinaryOp _ "-" expr1 expr2) = showParen (d > 3) $
                                                     showsPrec 3 expr1 .
                                                     showChar '-' .
                                                     showsPrec 3 expr2
        showsPrec d (S1BinaryOp _ "*" expr1 expr2) = showParen (d > 4) $
                                                     showsPrec 4 expr1 .
                                                     showChar '*' .
                                                     showsPrec 4 expr2
        showsPrec d (S1BinaryOp _ "/" expr1 expr2) = showParen (d > 4) $
                                                     showsPrec 4 expr1 .
                                                     showChar '/' .
                                                     showsPrec 4 expr2
        showsPrec _ (S1Block _ exprs) = showChar '{' .
                                        showsWithSep ";" exprs .
                                        showString ";}"
        showsPrec _ (S1If _ cond expr1 expr2) = showString "if " .
                                                showsPrec 0 cond .
                                                showString " then " .
                                                showsPrec 0 expr1 .
                                                showString " else " .
                                                showsPrec 0 expr2 .
                                                showString " fi"
        showsPrec _ (S1While _ cond expr) = showString "while " .
                                            showsPrec 0 cond .
                                            showString " loop " .
                                            showsPrec 0 expr .
                                            showString " pool"
        showsPrec _ (S1Let _ vars expr) = showString "let " .
                                          showsWithSep ", " (map (\(name, ctype, expr') -> if expr' == S1Void
                                                                                           then name ++ ":" ++ ctype
                                                                                           else name ++ ":" ++ ctype ++ " <- " ++ show expr') vars) .
                                          showString " in " .
                                          showsPrec 0 expr
        showsPrec _ (S1Case _ expr variants) = showString "case " .
                                               showsPrec 0 expr .
                                               showString " of " .
                                               showString (foldl1 (++) $ map (\(name, ctype, expr') -> name ++ ":" ++ ctype ++ " => " ++ (show expr') ++ ";") variants) .
                                               showString " esac"
        showsPrec d (S1Assign _ name expr) = showParen (d > 0) $ showString name .
                                                                 showString " <- " .
                                                                 showsPrec 0 expr
        showsPrec _ _ = error "Error when showing CExpr."

cTP :: TokenParser st
cTP = makeTokenParser $ emptyDef { commentStart   = "(*"
                                 , commentEnd     = "*)"
                                 , commentLine    = "--"
                                 , nestedComments = True
                                 , identStart     = letter
                                 , identLetter    = alphaNum <|> oneOf "_"
                                 , opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"              
                                 , reservedOpNames= ["<-", "<=", "<", "=", "+", "-", "*", "/", "~", "@", ".", ":"]
                                 , reservedNames  = ["class", "else", "false", "fi", "if", "in",
                                                     "inherits", "isvoid", "let", "loop", "pool",
                                                     "self", "then", "while", "case", "esac",
                                                     "new", "of", "not", "true"]
                                 , caseSensitive  = False                                   
                                 }

toTree :: S1Expr -> [(String, S1Expr, SourcePos)] -> S1Expr
toTree expr [] = expr
toTree expr1 ((op, expr2, pos):t) = toTree (S1BinaryOp pos op expr1 expr2) t

cProgram :: Parser S1Program
cProgram = do whiteSpace cTP
              program <- many cClass
              eof
              return program

featureMethod :: S1Feature -> Bool
featureMethod (FeatureMethod _) = True
featureMethod _ = False

cClass :: Parser S1Class
cClass = do pos <- getPosition
            reserved cTP "class"
            name <- cType
            ancestor <- (reserved cTP "inherits" >> cType) <|> return "Object"
            features <- braces cTP (many cFeature)
            _ <- semi cTP
            if name == "Object" || name == "Int" || name == "Bool" || name == "String" || name == "IO"
              then fail ("Invalid class name: " ++ name ++ " at " ++ show pos)
              else return (pos, name, ancestor, map (\(FeatureField field) -> field) $ filter (not . featureMethod) features, map (\(FeatureMethod method) -> method) $ filter featureMethod features)

cFeature :: Parser S1Feature
cFeature = do pos <- getPosition
              name <- cId
              (do cfeatureArgs <- parens cTP (commaSep cTP cIdType)
                  _ <- colon cTP
                  ctype <- cType
                  cexpr <- braces cTP cExpr
                  _ <- semi cTP
                  return (FeatureMethod (pos, name, ctype, cfeatureArgs, cexpr))
               <|>
               do _ <- colon cTP
                  ctype <- cType
                  cexpr <- (symbol cTP "<-" >> cExpr) <|> return S1Void
                  _ <- semi cTP
                  return (FeatureField (pos, name, ctype, cexpr)))

cExpr :: Parser S1Expr
cExpr = do pos <- getPosition
           name <- try $ do cid <- cId
                            _ <- symbol cTP "<-"
                            return cid
           cexpr <- cExpr
           return (S1Assign pos name cexpr)
        <|>
        cRelationNot

cRelationNot :: Parser S1Expr
cRelationNot = do pos <- getPosition
                  try $ reserved cTP "not"
                  cnot <- cRelationNot
                  return (S1UnaryOp pos "not" cnot)
               <|>
               cRelation

cRelation :: Parser S1Expr
cRelation = cAddition >>= cRelation'

cRelation' :: S1Expr -> Parser S1Expr
cRelation' caddition = do pos <- getPosition
                          op <- try (symbol cTP "<=") <|> symbol cTP "<" <|> symbol cTP "="
                          cnot <- cNot
                          return (S1BinaryOp pos op caddition cnot)
                       <|> return caddition

cNot :: Parser S1Expr
cNot = do pos <- getPosition
          try $ reserved cTP "not"
          cnot <- cNot
          return (S1UnaryOp pos "not" cnot)
       <|>
       cAddition

cAddition :: Parser S1Expr
cAddition = do firstMultiplication <- cMultiplication
               nextMultiplications <- many (do pos <- getPosition
                                               op <- symbol cTP "+" <|> symbol cTP "-"
                                               cmultiplication <- cMultiplication
                                               return (op, cmultiplication, pos))
               return (toTree firstMultiplication nextMultiplications)

cMultiplication :: Parser S1Expr
cMultiplication = do firstIsvoid <- cIsvoid
                     nextIsvoids <- many (do pos <- getPosition
                                             op <- symbol cTP "*" <|> symbol cTP "/"
                                             cisvoid <- cIsvoid
                                             return (op, cisvoid, pos))
                     return (toTree firstIsvoid nextIsvoids)

cIsvoid :: Parser S1Expr
cIsvoid = do pos <- getPosition
             try $ reserved cTP "isvoid"
             cisvoid <- cIsvoid
             return (S1UnaryOp pos "isvoid" cisvoid)
          <|>
          cNeg

cNeg :: Parser S1Expr
cNeg = do pos <- getPosition
          _ <- symbol cTP "~"
          cneg <- cNeg
          return (S1UnaryOp pos "~" cneg)
       <|>
       cDot

cDot :: Parser S1Expr
cDot = do cterm <- cTerm
          dots <- many cDot'
          return (dotToTree cterm dots)
       where dotToTree expr [] = expr
             dotToTree expr ((pos, ctype, name, args):t) = dotToTree (S1Dot pos expr ctype name args) t

cDot' :: Parser (SourcePos, String, String, [S1Expr])
cDot' = do ctype <- (symbol cTP "@" >> cType) <|> return ""
           pos <- getPosition
           _ <- dot cTP
           (name, args) <- cMethod
           return (pos, ctype, name, args)

cTerm :: Parser S1Expr
cTerm = do pos <- getPosition
           name <- cId
           (do args <- cArgs
               return (S1Dot pos (S1Self pos) "" name args)
            <|> return (S1Variable pos name))
        <|>
        parens cTP cExpr <|>
        cBlock <|>
        cIf <|>
        cWhile <|>
        cLet <|>
        cNew <|>
        cCase <|>
        cSelf <|>
        cTrue <|>
        cFalse <|>
        cString <|>
        cInteger

cBlock :: Parser S1Expr
cBlock = do pos <- getPosition
            cexprs <- braces cTP $ many1 (do cexpr <- cExpr
                                             _ <- semi cTP
                                             return cexpr)
            return (S1Block pos cexprs)

cNew :: Parser S1Expr
cNew = do pos <- getPosition
          reserved cTP "new"
          ctype <- cType
          return (S1New pos ctype)

cIf :: Parser S1Expr
cIf = do pos <- getPosition
         reserved cTP "if"
         cexpr1 <- cExpr
         reserved cTP "then"
         cexpr2 <- cExpr
         reserved cTP "else"
         cexpr3 <- cExpr
         reserved cTP "fi"
         return (S1If pos cexpr1 cexpr2 cexpr3)

cWhile :: Parser S1Expr
cWhile = do pos <- getPosition
            reserved cTP "while"
            cexpr1 <- cExpr
            reserved cTP "loop"
            cexpr2 <- cExpr
            reserved cTP "pool"
            return (S1While pos cexpr1 cexpr2)

cLet :: Parser S1Expr
cLet = do pos <- getPosition
          reserved cTP "let"
          idTypeExprs <- commaSep1 cTP cIdTypeExpr
          reserved cTP "in"
          cexpr <- cExpr
          return (S1Let pos idTypeExprs cexpr)

cCase :: Parser S1Expr
cCase = do pos <- getPosition
           reserved cTP "case"
           cond <- cExpr
           reserved cTP "of"
           cidTypeExprs <- many (do (cid, ctype) <- cIdType
                                    _ <- symbol cTP "=>"
                                    cexpr <- cExpr
                                    _ <- semi cTP
                                    return (cid, ctype, cexpr))
           reserved cTP "esac"
           return (S1Case pos cond cidTypeExprs)

cSelf :: Parser S1Expr
cSelf = do pos <- getPosition
           reserved cTP "self"
           return (S1Self pos)

cMethod :: Parser (String, [S1Expr])
cMethod = do name <- cId
             args <- cArgs
             return (name, args)


cArgs :: Parser [S1Expr]
cArgs = parens cTP $ commaSep cTP $ cExpr

cTrue :: Parser S1Expr
cTrue = do pos <- getPosition
           reserved cTP "true"
           return (S1True pos)

cFalse :: Parser S1Expr
cFalse = do pos <- getPosition
            reserved cTP "false"
            return (S1False pos)

cString :: Parser S1Expr
cString = do pos <- getPosition
             str <- stringLiteral cTP
             return (S1String pos str)

cInteger :: Parser S1Expr
cInteger = do pos <- getPosition
              val <- integer cTP
              return (S1Integer pos val)

cVariable :: Parser S1Expr
cVariable = do pos <- getPosition
               name <- cId
               return (S1Variable pos name)

cIdTypeExpr :: Parser (String, String, S1Expr)
cIdTypeExpr = do (cid, ctype) <- cIdType
                 cexpr <- (symbol cTP "<-" >> cExpr) <|> return S1Void
                 return (cid, ctype, cexpr)

cIdType :: Parser (String, String)
cIdType = do cid <- cId
             _ <- colon cTP
             ctype <- cType
             return (cid, ctype)

cId :: Parser String
cId = identifier cTP

cType :: Parser String
cType = identifier cTP