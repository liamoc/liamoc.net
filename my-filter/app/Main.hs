import System.Environment
import Image.LaTeX.Render
import Codec.Picture
import Control.Applicative
import System.FilePath
import qualified Data.ByteString.Base64.Lazy as B64
import qualified Data.ByteString.Lazy.Char8 as BS

formulaSettings :: String -> Bool -> FormulaOptions
formulaSettings pre display
  = if display then displaymath { preamble = pre }
               else math        { preamble = pre }

-- | Render errors nicely, in order to show any problems clearly, with all information intact.
displayError :: RenderError -> String
displayError ImageIsEmpty           = "<b>Error: The rendered image was empty </b>"
displayError CannotDetectBaseline   = "<b>Error: Cannot detect baseline in rendered image </b>"
displayError (LaTeXFailure str)     = "<b>LaTeX failed: <br/><pre>" ++ processString str ++ "</pre></b>"
displayError (DVIPSFailure str)     = "<b>DVIPS failed: <br/><pre>" ++ processString str ++ "</pre></b>"
displayError (IMConvertFailure str) = "<b>convert failed: <br/><pre>" ++ processString str ++ "</pre></b>"
displayError (ImageReadError str)   = "<b>Error reading image: <br/><pre>" ++ processString str ++ "</pre></b>"
displayError (IOException e)        = "<b>IO Exception:<br/><pre>" ++ show e ++ "</pre></b>"



dims :: Image a -> (Int,Int)
dims = liftA2 (,) imageWidth imageHeight

dimensions :: DynamicImage -> (Int,Int)
dimensions (ImageRGB8 i)   = dims i
dimensions (ImageRGBA8 i)  = dims i
dimensions (ImageRGB16 i)  = dims i
dimensions (ImageRGBA16 i) = dims i
dimensions (ImageY8 i)     = dims i
dimensions (ImageY16 i)    = dims i
dimensions (ImageYA8 i)    = dims i
dimensions (ImageYA16 i)   = dims i
dimensions _               = error "Unsupported image format somehow!"
convertFormulaDataURI
  :: FormulaOptions -> Bool
  -> String -> IO String
convertFormulaDataURI f disp s = imageForFormula defaultEnv f s >>= \x -> case x of 
   Left e -> return $ displayError e
   Right (b,i) -> let
       Right bs = encodeDynamicPng i
       dataUri = "data:image/png;base64," ++ BS.unpack (B64.encode bs)
       (ow,oh) = dimensions i
       (w,h) = (round (fromIntegral ow / 1.5), round (fromIntegral oh / 1.5)) :: (Int,Int)
     in return $ 
        "<img width="  ++ show w ++
            " alt=\"" ++ processString s ++ "\"" ++
            " height=" ++ show h ++
            " src=\""  ++ dataUri ++ "\"" ++
            " class="  ++ (if disp then "display-math" else "inline-math") ++
            " style=\"margin:0; vertical-align:-" ++ show (round (fromIntegral b / 1.5) :: Int) ++ "px;\"/>"

processString = (>>= \x -> case x of
                 '<'  -> "&lt;"
                 '>'  -> "&gt;"
                 '&'  -> "&amp;"
                 '"'  -> "&quot;"
                 '\'' -> "&39;"
                 '\n' -> " "
                 '\r' -> " "
                 '\t' -> " "
                 x    -> [x])
convertFormulaDataURIWith _ _ x = return x
main :: IO ()
main = do 
  preamble <- readFile "preamble"
  [display] <- getArgs 
  string <- getContents
  putStrLn =<< convertFormulaDataURI (formulaSettings preamble (display == "DisplayMath")) (display == "DisplayMath") string

