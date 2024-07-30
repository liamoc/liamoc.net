function splat_popen(data,cmd, argt)
   temp = io.open("temp.tex","w")
   io.output(temp)
   io.write(data);
   io.close(temp)
   os.execute(cmd .. " " .. argt .. "< temp.tex > temp.html")
   outf = io.open("temp.html","rb")
   content = outf:read("*all")
   outf:close()
   os.execute("rm -f temp.tex temp.html")
   return content
end
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
return {
  {
    Math = function(m)
      out = splat_popen(m.text,"my-filter-exe", m.mathtype)
      return pandoc.RawInline("html", out)
    end,
  }
}
