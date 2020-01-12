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

base_name = string.gsub(PANDOC_STATE.input_files[1],"%..*","")
extension = string.gsub(PANDOC_STATE.input_files[1],".*%.","")
extension = string.gsub(extension,".*%.","")
junk = ""
f = io.open(string.gsub(base_name,"^posts","dependencies") .. ".d", "w")
io.output(f)
io.write("out/" .. base_name .. "/index.html: ")
return {
  {
    Image = function(img)
       if string.find(img.src, "^%./images/") then
          io.write("out/" .. base_name .."/" .. string.gsub(img.src,"^%./","") .. " ")
          junk = junk .. "out/" .. base_name .."/" .. string.gsub(img.src,"^%./","") .. ": post_" .. string.gsub(img.src,"^%./","") .. "\n"
          junk = junk .. "\t@echo '$(BOLD)" .. string.gsub(base_name,"^posts%/","") ..":$(SGR0)$(PALEBLUE) Copying dependency $(BOLD)" .. string.gsub(img.src,"^%./","") .. "$(SGR0)' \n"
          junk = junk .. "\t@mkdir -p $(@D) && cp $< $@\n"
       end
    end,
    Pandoc = function(pdoc)
      io.write("out/" .. base_name .. "/cites.bib ")
      io.write("out/" .. base_name .. "/preamble ")
      io.write("out/" .. base_name .. "/index." .. extension .. "\n")
      io.write(junk)
      io.close(f)
      return pandoc.Pandoc({})
    end,
  }
}
