module Main where

import System.Environment
import Data.Either
import Text.ParserCombinators.Parsec
import System.Process
import System.Directory
import Syntax
import Semantics
import CodeGeneration
import CIL

getPreferences :: [String] -> Bool -> String -> String -> Bool -> Bool -> ([String], Bool, String, String, Bool, Bool)
getPreferences [] stdout outName ilasm noil noexe = ([], stdout, outName, ilasm, noil, noexe)
getPreferences args@(h:t) stdout outName ilasm noil noexe =
        case h of
          "--stdout" -> getPreferences t True outName ilasm noil noexe
          "-o"       -> getPreferences (tail t) stdout (head t) ilasm noil noexe
          "--ilasm"  -> getPreferences (tail t) stdout outName (head t) noil noexe
          "--noil"   -> getPreferences t stdout outName ilasm True noexe
          "--noexe"  -> getPreferences t stdout outName ilasm noil True
          _          -> (args, stdout, outName, ilasm, noil, noexe)

main :: IO ()
main = do args <- getArgs
          let (args', stdout, outName, ilasm, noil, noexe) = getPreferences args False "out" "ilasm" False False
              outName' = outName ++ ".il"
          prog <- getProgName
          if null args'
            then putStrLn $ "Usage: " ++ prog ++ " [file1, file2, ...]"
            else do parseResults <- fmap (map (\(name, content) -> parse cProgram name content)) $ fmap (zip args') $ mapM readFile args'
                    let parseFails = lefts parseResults
                        s1program = concat $ rights parseResults
                        semanticsResult = semanticsCheck s1program
                    if not $ null parseFails
                      then mapM_ (putStrLn . show) parseFails
                      else case semanticsResult of
                             Left errors -> mapM_ putStrLn errors
                             Right (s2program, parents, classMappings) ->
                                do let cil = generateCIL classMappings $ translateProgram parents classMappings s2program
                                   if stdout then putStrLn cil else return ()
                                   writeFile outName' cil
                                   if not noexe then runCommand (ilasm ++ " " ++ outName') >>= waitForProcess >> return () else return ()
                                   if noil then removeFile outName' else return ()