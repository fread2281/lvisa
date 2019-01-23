module Main where


-- import Solver.Class
-- import Frontend.Elab
-- import Core

-- main = pure ()

-- import MonadTac
-- import Text.Megaparsec (runParser, parseErrorPretty)
import Lib.Pretty (prettyPrint)
import Frontend.Parser (expr,defns)
import Frontend.Elab
import Frontend.Indentation
import Solver.MonadTacImpl
import Solver.MonadTac
import Core (Env(EmptyEnv))
import Options.Applicative hiding (Success, Failure)
import Text.Parsix (parseText, parseFromFileEx, Result(..), prettyError, eof)
import Solver.Pretty
import Core
import Data.IORef
import Lib.Misc

data Options = Options {
  debug :: Bool,
  interactive :: Bool,
  eval :: Maybe Text,
  file :: Maybe String
} deriving (Show)

opts :: Parser Options
opts = Options
  <$> switch (short 'd' <> long "debug" <> help "Print debug info")
  <*> switch (short 'i' <> long "interactive" <> help "Run in interactive mode")
  <*> optional (strOption (short 'e' <> long "eval" <> metavar "EXPR" <> help "Evaluate and print an expression"))
  <*> optional (strArgument (metavar "FILE" <> help "File to compile/load"))


main :: IO ()
main = execParser
  (info (helper <*> opts)
  (fullDesc <> progDesc "The lang programming language"))
  >>= \o ->
  if | interactive o -> error "Interactive mode not yet implemented"
     | Just e <- eval o -> do
        let x = parseText (runIndentT (expr <* eof)) e "<expr>"
        case x of
          Failure v -> print $ prettyError v
          Success v -> do
            prettyPrint =<< (runElabMonad $ do
              p <- prelude
              elabInfer EmptyEnv p v)
      --  | Just fn <- file o -> do
     | otherwise -> do
        let fn = maybe "lib/nat.lang" id $ file o
         -- x <- readFile fn <&> parseText defns fn
        x <- parseFromFileEx (runIndentT (defns <* eof)) fn
        case x of
          Failure v -> print $ prettyError v
          Success v -> do
            when (debug o) $ prettyPrint v
            ((r,d),s) <- runElabMonad $ do
              p <- prelude
              dfns <- elabDefinitions EmptyEnv p v
              loop_solve
              zonk_state
              st <- use id
              (dfns,) <$> prettyState st
            putStrLn "Debug output:"
            prettyPrint r >> prettyPrint s
            readIORef displayedMetas >>= print . prettyMetas
            print d
            pure ()

-- solve_constraints = go where
--   go cs = _


-- localize_errors m = do
--   (x, s) <- runElabMonad m
--   let cs = constrsints cs
--   _

