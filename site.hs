--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings, LambdaCase, ViewPatterns #-}
import           Data.Monoid         ((<>))
import           Hakyll.Core.Compiler
import           Hakyll.Core.File
import           Hakyll.Core.Identifier
import           Hakyll.Core.Identifier.Pattern
import           Hakyll.Core.Item
import           Hakyll.Core.Metadata
import           Hakyll.Core.Routes
import           Hakyll.Core.Rules
import           Hakyll.Main
import           Hakyll.Web.CompressCss
import           Hakyll.Web.Feed
import           Hakyll.Web.Html.RelativizeUrls
import           Hakyll.Web.Pandoc
import           Hakyll.Web.Pandoc.Biblio -- BiblioWorkaround
import           Hakyll.Web.Tags
import           Hakyll.Web.Template
import           Hakyll.Web.Template.Context
import           Hakyll.Web.Template.List
import qualified Data.Map as M
import Text.Pandoc.Options
import Text.Pandoc
import System.Directory
import qualified Data.Set as S
import System.FilePath
import Data.Maybe
import Control.Exception (bracket)
import Network.URI
import Agda.Contrib.Snippets
import Control.Memoization.Utils
import Image.LaTeX.Render.Pandoc
import Image.LaTeX.Render
import Data.Char(isSpace)
agdaOpts :: CommandLineOptions
agdaOpts = defaultOptions

readerSettings :: ReaderOptions
readerSettings = def { readerSmart = True, readerOldDashes = True, readerExtensions = S.insert Ext_pipe_tables pandocExtensions  }

writerSettings :: WriterOptions
writerSettings = def { writerHighlight = True }

defaultPreamble :: String
defaultPreamble = ""

formulaSettings :: String -> PandocFormulaOptions
formulaSettings pre
  = defaultPandocFormulaOptions
      { formulaOptions = \case DisplayMath -> displaymath { preamble = pre }
                               _           -> math        { preamble = pre }
      }

feedConfiguration :: FeedConfiguration
feedConfiguration = FeedConfiguration
    { feedTitle       = "liamoc.net"
    , feedDescription = "Musings of Liam O'Connor, lambda scientist"
    , feedAuthorName  = "Liam O'Connor"
    , feedAuthorEmail = "me@liamoc.net"
    , feedRoot        = "http://liamoc.net"
    }

type CacheSize = Integer

initFormulaRendererDataURI :: CacheSize -> EnvironmentOptions
                           -> IO (PandocFormulaOptions -> Item Pandoc -> Compiler (Item Pandoc))
initFormulaRendererDataURI cs eo = do
    mImageForFormula <- curry <$> memoizeLru (Just cs) (uncurry drawFormula)
    let eachFormula x y = do
          putStrLn $ "    formula (" ++ environment x ++ ") \"" ++ equationPreview y ++ "\""
          mImageForFormula x y
    return $ \fo -> withItemBody $ unsafeCompiler . convertAllFormulaeDataURIWith eachFormula fo
  where
    drawFormula x y = do
      putStrLn "      drawing..."
      imageForFormula eo x y
    equationPreview (dropWhile isSpace -> x)
      | length x <= 16 = x
      | otherwise      = take 16 $ filter (/= '\n') x ++ "..."

--------------------------------------------------------------------------------
main :: IO ()
main = do
  renderEquations <- initFormulaRendererDataURI 1000 defaultEnv
  hakyll $ do
    tags <- buildTags ("posts/*.markdown" .||. "posts/*.lagda" .||. "posts/*.org") (fromCapture "tags/*.html")

    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "agda-lib/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "js/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "js/patterns/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match (fromList ["about.rst", "contact.markdown"]) $ do
        route   $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    match "cites/*.bib" $ compile biblioCompiler
    match "association-for-computing-machinery.csl" $ compile cslCompiler


    match ("posts/*.markdown" .||. "posts/*.lagda" .||. "posts/*.org") $ do
        route $ setExtension "html"

        compile $ do

            pr <- fmap (fromMaybe defaultPreamble . M.lookup "preamble") (getMetadata =<< getUnderlying)
            fp <- flip replaceExtension "bib" . flip replaceDirectory "cites/" <$> getResourceFilePath

            let readPandoc' i = do
                  exists <- unsafeCompiler $ doesFileExist fp
                  if exists then do
                    csl <- load "association-for-computing-machinery.csl"
                    bib <- load (fromFilePath fp)
                    readPandocBiblio readerSettings csl bib i
                  else
                    readPandocWith readerSettings i

                writePandoc' = return . writePandocWith writerSettings

            getResourceBody
              >>= agdaCompiler agdaOpts
              >>= changeItemExtension readPandoc'
              >>= renderEquations (formulaSettings pr)
              >>= writePandoc'
              >>= loadAndApplyTemplate "templates/post.html"    (tagsCtx tags)
              >>= saveSnapshot "content"
              >>= loadAndApplyTemplate "templates/disqus.html"  (tagsCtx tags)
              >>= loadAndApplyTemplate "templates/default.html" (tagsCtx tags)
              >>= relativizeUrls

    create ["archive.html"] $ do
        route idRoute
        compile $ do
            let archiveCtx = field "posts" (\_ -> postList' recentFirst)
                           <> constField "title" "Archives"
                           <> defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
                >>= loadAndApplyTemplate "templates/default.html" archiveCtx
                >>= relativizeUrls

    tagsRules tags $ \tag pattern -> do
        let title = "Posts tagged " ++ tag
        route idRoute
        compile $ do
            list <- postList tags pattern recentFirst
            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html"
                        (constField "title" title <>
                            constField "posts" list <>
                            defaultContext)
                >>= loadAndApplyTemplate "templates/default.html"
                        (constField "title" title <>
                            defaultContext)
                >>= relativizeUrls

    match "index.html" $ do
        route idRoute
        compile $ do
            let indexCtx = field "posts" (const $ postList' (\x -> take 3 <$> recentFirst x))
                         <> field "tagcloud" (const $ renderTagCloud 75 150 tags)
            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" postCtx
                >>= relativizeUrls

    create ["atom.xml"] $ do
        route idRoute
        compile $ do
            posts <- take 10  <$> (recentFirst =<< loadAllSnapshots "posts/*" "content")
            renderAtom feedConfiguration feedCtx posts

    create ["rss.xml"] $ do
        route idRoute
        compile $ do
            posts <- take 10 <$> (recentFirst =<< loadAllSnapshots "posts/*" "content")
            renderRss feedConfiguration feedCtx posts

    match "templates/*" $ compile templateCompiler




--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" <>
    defaultContext

feedCtx :: Context String
feedCtx = postCtx <> bodyField "description"

--------------------------------------------------------------------------------
postList' :: ([Item String] -> Compiler [Item String]) -> Compiler String
postList' sortFilter = do
    posts   <- sortFilter =<< loadAll "posts/*"
    itemTpl <- loadBody "templates/post-item.html"
    applyTemplateList itemTpl postCtx posts

postList :: Tags -> Pattern -> ([Item String] -> Compiler [Item String])
         -> Compiler String
postList tags pattern preprocess' = do
    postItemTpl <- loadBody "templates/post-item.html"
    posts <- preprocess' =<< loadAll pattern
    applyTemplateList postItemTpl (tagsCtx tags) posts

tagsCtx :: Tags -> Context String
tagsCtx tags =
    tagsField "taglinks" tags <>
    postCtx

---
isAgda :: Item a -> Bool
isAgda i = ex == ".lagda"
  where ex = snd . splitExtension . toFilePath . itemIdentifier $ i

agdaCompiler :: CommandLineOptions -> Item String -> Compiler (Item String)
agdaCompiler aopt i =
     if isAgda i
          then cached cacheName $
               do fp <- getResourceFilePath
                  unsafeCompiler $ bracket getCurrentDirectory setCurrentDirectory $ const $
                      do abfp <- canonicalizePath fp
                         setCurrentDirectory (dropFileName abfp)
                         s <- renderAgdaSnippets aopt "Agda" (fromJust $ parseURIReference "/agda-lib/")  abfp
                         return $ i {itemBody = s}
          else return i
  where
    cacheName = "LiterateAgda.agdaCompiler"

changeItemExtension :: (Item a -> Compiler (Item b)) -> Item a -> Compiler (Item b)
changeItemExtension f i = let fn = toFilePath $ itemIdentifier i
                           in do x <- f (i {itemIdentifier = fromFilePath $ fn -<.> "markdown" })
                                 return $ x {itemIdentifier = fromFilePath fn }
