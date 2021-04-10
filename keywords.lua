function dump(o)
   if type(o) == 'table' then
      local s = '{ '
      for k,v in pairs(o) do
         if type(k) ~= 'number' then k = '"'..k..'"' end
         s = s .. '['..k..'] = ' .. dump(v) .. ','
      end
      return s .. '} '
   else
      return tostring(o)
   end
end
function file_exists(name)
   local f=io.open(name,"r")
   if f~=nil then io.close(f) return true else return false end
end
os.execute("mkdir -p tags")
return {
  {
    Pandoc = function(pdoc)
      entry = string.format(" - [%s](/%s/index.html) - %s\n", pandoc.utils.stringify(pdoc.meta.title), string.gsub(PANDOC_STATE.input_files[1],"%..*",""), pandoc.utils.stringify(pdoc.meta.date))
      for i,v in ipairs(pdoc.meta.keywords) do
          ta = string.gsub(pandoc.utils.stringify(v),",","");
          tag = string.gsub(ta," ","");
          if tag ~= '' then
          if not file_exists("tags/" .. tag .. ".md") then 
             file = io.open("tags/" .. tag .. ".md","a")
             io.output(file)
             io.write("---\ntitle: \"Tag: " .. tag .. "\"\n---\n");
             io.close(file)
          end
          file = io.open("tags/" .. tag .. ".md","a")
          io.output(file)
          io.write(entry)
          io.close(file)
          end
      end
      return pandoc.Pandoc({})
    end,
  }
}
