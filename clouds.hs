

blah :: [String] -> (Integer, String)
blah (y:x) = (read y, concat x)
main = do
  x <- fmap (map (blah . words) . lines)  getContents
  let mn = minimum (map fst (filter ((/= "") . snd) x))
  let mx = maximum (map fst (filter ((/= "") . snd) x))
  let scale = mx - mn;
  let minFont = 75
  let maxFont = 150
  flip mapM x $ \(v,s) -> 
   if s /= "" then  do
     let ratio = fromInteger (v - mn) / fromInteger (scale)
     let fontSize = ratio * (maxFont - minFont) + minFont
     let t =  takeWhile (/= '.') s
     putStrLn $ "<a style='font-size:" ++ show fontSize ++ "%;' href='/" ++ t ++ ".html' >" ++ drop 1(dropWhile (/= '/') t) ++ "</a>"
   else return () 
