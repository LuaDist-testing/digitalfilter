#!/usr/local/bin/lua
---------------------------------------------------------------------
--     This Lua5 script is Copyright (c) 2017, Peter J Billam      --
--                       www.pjb.com.au                            --
--  This script is free software; you can redistribute it and/or   --
--         modify it under the same terms as Lua5 itself.          --
---------------------------------------------------------------------
-- transforms:
-- 1) from polepair to b0b1b2
-- 2) from freq,samplerate to k
-- 3) from a0a1a2b0b1b2, k to A0A1A2B0B1B2   p.56
-- 4) normalise A0A1A2B0B1B2 so that A0+A1+A2=B0+B1+B2
local Version = '1.0  for Lua5'
local VersionDate  = '12jul2017';
local Synopsis = [[
program_name [options] [filenames]
]]
local iarg=1; while arg[iarg] ~= nil do
	if not string.find(arg[iarg], '^-[a-z]') then break end
	local first_letter = string.sub(arg[iarg],2,2)
	if first_letter == 'v' then
		local n = string.gsub(arg[0],"^.*/","",1)
		print(n.." version "..Version.."  "..VersionDate)
		os.exit(0)
	elseif first_letter == 'c' then
		whatever()
	else
		local n = string.gsub(arg[0],"^.*/","",1)
		print(n.." version "..Version.."  "..VersionDate.."\n\n"..Synopsis)
		os.exit(0)
	end
	iarg = iarg+1
end
-- local R  = require 'randomdist'
local DF = require 'digitalfilter'
require 'DataDumper'

----------------------------- infrastructure

local function round(x) return math.floor(x+0.5) end

function dump(x)
    local function tost(x)
        if type(x) == 'table' then return 'table['..tostring(#x)..']' end
        if type(x) == 'string' then return "'"..x.."'" end
        if type(x) == 'function' then return 'function' end
        if x == nil then return 'nil' end
        return tostring(x)
    end
    if type(x) == 'table' then
        local n = 0 ; for k,v in pairs(x) do n=n+1 end
        if n == 0 then return '{}' end
        local a = {}
        if n == #x then for i,v in ipairs(x) do a[i] = tost(v) end
        else for k,v in pairs(x) do a[#a+1] = tostring(k)..'='..tost(v) end
        end
        return '{ '..table.concat(a, ', ')..' }'
    end
    return tost(x)
end

function warn(...)
    local a = {}
    for k,v in pairs{...} do table.insert(a, tostring(v)) end
    io.stderr:write(table.concat(a),'\n') ; io.stderr:flush()
end
function eq (a,b,eps)
	if not eps then eps = .000001 end
	return math.abs(a-b) < eps
end
function die(...) warn(...);  os.exit(1) end
function avabs (a)
	local tot = 0.0
	for i,v in ipairs(a) do tot = tot + math.abs(a[i]) end
	return tot / #a
end
function rms (arr)
	local tot = 0.0
	for i,v in ipairs(arr) do tot = tot + v*v end
	return math.sqrt(tot / #arr)
end

---------------------------------- start testing
 
Test = 12 ; i_test = 0; Failed = 0;
function ok(b,s)
    i_test = i_test + 1
    if b then
        io.write('ok '..i_test..' - '..s.."\n")
		return true
    else
        io.write('not ok '..i_test..' - '..s.."\n")
        Failed = Failed + 1
		return false
    end
end
ok(eq(1.0, 0.99, 0.02), 'eq(1.0,0.99,0.02)  is true')
ok(not eq(1.0, 0.99, 0.005),'eq(1.0,0.99,0.005) is false')

local freq,Q = DF.pole_pair_to_freq_Q(-0.70710678, 0.70710678)
ok(eq(freq,1) and eq(Q,math.sqrt(0.5)),
 'pole_pair_to_freq_Q returned freq='..tostring(freq)..'  Q='..tostring(Q))

local sections = assert(DF.freq_sections({
	['type']        = 'butterworth',
	['shape']       = 'highpass',
	['order']       = 2,
   	['freq']        = 1000,
  	['samplerate']  = 44100,
  	-- ['debug']       = true,
}))
local a0 = sections[1][1]
local a1 = sections[1][2]
local a2 = sections[1][3]
local b0 = sections[1][4]
local b1 = sections[1][5]
local b2 = sections[1][6]
-- print(DataDumper(sections))
-- { { 0, 0, 1, 2.5330295825574e-08, 0.00022507907941697, 1 } }
--if not ok(a0==0 and a1==0 and a2==1 and
--  eq(b0,2.533029e-8, 1.0e-11) and eq(b1,0.000225079) and b2==1,
--  'freq_sections: butterworth highpass') then
--	warn(' a0=',a0,' a1=',a1,' a2=',a2,'\n b0=',b0,' b1=',b1,' b2=',b2)
--end
if not ok(a0==0 and a1==0 and eq(a2,2.533029e-8, 1.0e-11) and
  eq(b0,1) and eq(b1,0.000225079) and eq(b2,2.533029e-8, 1.0e-11),
  'freq_sections: butterworth highpass') then
    warn(' a0=',a0,' a1=',a1,' a2=',a2,'\n b0=',b0,' b1=',b1,' b2=',b2)
end
local freq,Q = DF.b0b1b2_to_freq_Q(b0,b1,b2)
if not ok(eq(freq,1000,0.01) and eq(Q,math.sqrt(0.5),0.0001),
  'freq='..tostring(freq)..'  Q='..tostring(Q)) then
	warn(' a0=',a0,' a1=',a1,' a2=',a2,'\n b0=',b0,' b1=',b1,' b2=',b2)
end

local sections = assert(DF.freq_sections({
	['type']        = 'butterworth',
	['shape']       = 'lowpass',
	['order']       = 2,
   	['freq']        = 1000,
  	['samplerate']  = 44100,
  	['Q']           = 3,
  	-- ['debug']       = true,
}))
a0 = sections[1][1] ; a1 = sections[1][2] ; a2 = sections[1][3]
b0 = sections[1][4] ; b1 = sections[1][5] ; b2 = sections[1][6]
-- {{ 1,0,2.5330295910584e-08, 1,5.3051647697298e-05,2.5330295910584e-08 }}
if not ok(a0==1 and a1==0 and a2==0 and b0==1 and
    eq(b1,0.000225079) and eq(b2,2.533029e-8,1e-12),
  'freq_sections: butterworth lowpass') then
	warn(' a0=',a0,' a1=',a1,' a2=',a2,'\n b0=',b0,' b1=',b1,' b2=',b2)
end
freq,Q = DF.b0b1b2_to_freq_Q(b0,b1,b2)
if not ok(eq(freq,1000,0.01) and eq(Q,math.sqrt(0.5),0.0001),
  'freq='..tostring(freq)..'  Q='..tostring(Q)) then
	warn(' a0=',a0,' a1=',a1,' a2=',a2,'\n b0=',b0,' b1=',b1,' b2=',b2)
end

-- os.exit()

local sections = assert(DF.freq_sections({
	['type']        = 'butterworth',
	['shape']       = 'lowpass',
	['order']       = 2,
   	['freq']        = 22200,
  	['samplerate']  = 44100,
}))
a0 = sections[1][1] ; a1 = sections[1][2] ; a2 = sections[1][3]
b0 = sections[1][4] ; b1 = sections[1][5] ; b2 = sections[1][6]
if not ok(a0==0 and a1==0 and a2==0 and b0==1 and b1==0 and b2==0,
  'lowpass  with freq>samplerate/2 is handled correctly') then
	warn(' a0=',a0,' a1=',a1,' a2=',a2,'  b0=',b0,' b1=',b1,' b2=',b2)
end
--os.exit()

sections = assert(DF.freq_sections({
	['type']        = 'butterworth',
	['shape']       = 'bandpass',
	['order']       = 2,
   	['freq']        = 22200,
  	['samplerate']  = 44100,
}))
a0 = sections[1][1]
a1 = sections[1][2]
a2 = sections[1][3]
b0 = sections[1][4]
b1 = sections[1][5]
b2 = sections[1][6]
if not ok(a0==0 and a1==0 and a2==0 and b0==1 and b1==0 and b2==0,
  'bandpass with freq>samplerate/2 is handled correctly') then
	warn(' a0=',a0,' a1=',a1,' a2=',a2,'  b0=',b0,' b1=',b1,' b2=',b2)
end

local sections = assert(DF.freq_sections({
	['type']        = 'butterworth',
	['shape']       = 'highpass',
	['order']       = 2,
   	['freq']        = 22200,
  	['samplerate']  = 44100,
}))
a0 = sections[1][1]
a1 = sections[1][2]
a2 = sections[1][3]
b0 = sections[1][4]
b1 = sections[1][5]
b2 = sections[1][6]
if not ok(a0==1 and a1==0 and a2==0 and b0==1 and b1==0 and b2==0,
  'highpass with freq>samplerate/2 is handled correctly') then
	warn(' a0=',a0,' a1=',a1,' a2=',a2,'  b0=',b0,' b1=',b1,' b2=',b2)
end

local sections = assert(DF.freq_sections({
	['type']        = 'butterworth',
	['shape']       = 'bandstop',
	['order']       = 2,
   	['freq']        = 22200,
  	['samplerate']  = 44100,
}))
a0 = sections[1][1]
a1 = sections[1][2]
a2 = sections[1][3]
b0 = sections[1][4]
b1 = sections[1][5]
b2 = sections[1][6]
if not ok(a0==1 and a1==0 and a2==0 and b0==1 and b1==0 and b2==0,
  'bandstop with freq>samplerate/2 is handled correctly') then
	warn(' a0=',a0,' a1=',a1,' a2=',a2,'  b0=',b0,' b1=',b1,' b2=',b2)
end

-- os.exit()

-- XXX

function new_sinewave (frequency, samplerate)   -- RMS amplitude = 1.0
	local angle = 0
	local delta_angle = 2 * math.pi * frequency / samplerate
	return function ()
		local s =  1.41413562373 * math.sin(angle)
		angle = angle + delta_angle
		return s
	end
end
--------------------------------- check the gain at zero frequency
-- local my_testsine = new_sinewave(,samplerate)
for i,filtertype in ipairs({'butterworth','bessel'}) do
	for order = 1,7 do
		local my_filter = DF.new_digitalfilter ({
			['type']        = filtertype,
			['shape']       = 'lowpass',
			['order']       = order,
   			['freq']        = 1000,
  			['samplerate']  = 44100,
--   			['debug']       = true,
		})
		local a = {}
		for i = 1,10000 do local dump = my_filter(1.0) end
		for i = 1,2000 do a[i] = my_filter(1.0) end
--print(DataDumper(a))
		amp = rms(a)
		ok(amp>0.98 and amp<1.02,
	  	filtertype..' order '..tostring(order)..
		  ' lowpass gain at 0 Hz = '..tostring(amp))
		if Failed >= 9 then die(' bailing out') end
	end
end

--------------------------------- check the gain at zero frequency
-- local my_testsine = new_sinewave(,samplerate)
local filtertype = 'chebyschev'
for order = 1,7 do
	local my_filter = DF.new_digitalfilter ({
		['type']        = filtertype,
		['shape']       = 'lowpass',
		['order']       = order,
   		['freq']        = 1000,
  		['samplerate']  = 44100,
--  		['debug']       = true,
	})
	local a = {}
--	for i = 1,2000 do a[i] = my_filter(1.0) end
--print(DataDumper(a))
--	amp = rms(a)
--	ok(amp>0.98 and amp<1.02,
--  	filtertype..' order '..tostring(order)..
--	  ' lowpass gain at 0 Hz = '..tostring(amp))
--	if Failed >= 9 then die(' bailing out') end
end

-- os.exit()

--------------------------------- plot some frequency responses ...
local frequencies = {
	  100,  112,  126,  141,  159,  178,
	  200,  224,  252,  282,  318,  356,
	  400,  448,  504,  566,  636,  673, 712, 755,
	  800,  842,  890,  943, 1000, 1062, 1126, 1196, 1268, 1421,
	 1510, 1600, 1693, 1792, 2016, 2264, 2544, 2848,
	 3200, 3684, 4032, 4528, 5088, 5696,
	 6400, 7368, 8064, 9056,10176,11392,
	12800,14736,16128,18112,20352,
}

-- os.exit()

------------------------------------------ bandpass
local samplerate  = 44100
local centre_freq = 1000
local my_testsine = new_sinewave(centre_freq,samplerate)
local plotfile = assert(io.open('/tmp/bandpass.plot', 'w'))
local Q = 4
for ifreq,frequency in ipairs(frequencies) do
	local a = {}
	local amps = {}
	for i = 1,2000 do a[#a+1] = my_testsine() end
	order = 2
	local my_sinewave  = new_sinewave(frequency,samplerate)
	local my_filter = DF.new_digitalfilter ({
		['type']        = 'butterworth',
		['shape']       = 'bandpass',
		['order']       = order,
   		['freq']        = centre_freq,
   		['samplerate']  = samplerate,
   		['Q']  = Q,
	})
	for i = 1,10000 do local dump = my_filter(my_sinewave()) end
	for i = 1,2000 do a[i] = my_filter(my_sinewave()) end
	amps[order] = rms(a)
	if frequency == 1000 then
		ok(eq(amps[order], 4.0, 0.01), 'bandpass '..tostring(order)..
		  ' gain at 1000Hz was '..tostring(amps[order]))
	end
	plotfile:write(string.format("%d %g\n", frequency, amps[2]))
end
plotfile:close()
local gp = assert(io.open('/tmp/bandpass.gp', 'w'))
gp:write([[
set terminal jpeg enhanced size 950,505 font "sans, 16"
set colorsequence classic
set output "/tmp/bandpass.jpg"
set xlabel "Centre frequency ]]..tostring(centre_freq)..[["
set ylabel "2nd-order bandpass Q=]]..tostring(Q)..[["
set logscale y
set yr [0.1:1.0]
set logscale x
set xr [100:10000]
plot "/tmp/bandpass.plot" using 1:2 w l axes x1y2 smooth bezier
]])
gp:close()
os.execute("gnuplot /tmp/bandpass.gp")
os.execute("display /tmp/bandpass.jpg &")

------------------------------------------ bandstop
local samplerate  = 44100
local centre_freq = 1000
local my_testsine = new_sinewave(centre_freq,samplerate)
local plotfile = assert(io.open('/tmp/bandstop.plot', 'w'))
local Q = 4
for ifreq,frequency in ipairs(frequencies) do
	local a = {}
	local amps = {}
	for i = 1,2000 do a[#a+1] = my_testsine() end
	order = 2
	local my_sinewave  = new_sinewave(frequency,samplerate)
	local my_filter = DF.new_digitalfilter ({
		['type']        = 'butterworth',
		['shape']       = 'bandstop',
		['order']       = order,
   		['freq']        = centre_freq,
   		['samplerate']  = samplerate,
   		['Q']  = Q,
	})
	for i = 1,10000 do local dump = my_filter(my_sinewave()) end
	for i = 1,2000 do a[i] = my_filter(my_sinewave()) end
	amps[order] = rms(a)
	if frequency == 1000 then
		ok(eq(amps[order], 0.013557), 'bandstop '..tostring(order)..
		  ' gain at 1000Hz was '..tostring(amps[order]))
	end
	plotfile:write(string.format("%d %g\n", frequency, amps[2]))
end
plotfile:close()
local gp = assert(io.open('/tmp/bandstop.gp', 'w'))
gp:write([[
set terminal jpeg enhanced size 950,505 font "sans, 16"
set colorsequence classic
set output "/tmp/bandstop.jpg"
set xlabel "Centre frequency ]]..tostring(centre_freq)..[["
set ylabel "2nd-order bandstop Q=]]..tostring(Q)..[["
set logscale y
set yr [0.1:1.0]
set logscale x
set xr [100:10000]
plot "/tmp/bandstop.plot" using 1:2 w l axes x1y2 smooth bezier
]])
gp:close()
os.execute("gnuplot /tmp/bandstop.gp")
os.execute("display /tmp/bandstop.jpg &")

-- os.exit()

------------------------------------------ butterworth_lp
local samplerate  = 44100
local cutoff_freq = 1000
local my_testsine = new_sinewave(cutoff_freq,samplerate)
local plotfile = assert(io.open('/tmp/butterworth_lp.plot', 'w'))
for ifreq,frequency in ipairs(frequencies) do
	local a = {}
	local amps = {}
	for i = 1,2000 do a[#a+1] = my_testsine() end
	for order = 1,7 do
		local my_sinewave  = new_sinewave(frequency,samplerate)
		local my_filter = DF.new_digitalfilter ({
			['type']        = 'butterworth',
			['shape']       = 'lowpass',
			['order']       = order,
       		['freq']        = cutoff_freq,
      		['samplerate']  = samplerate,
		})
		for i = 1,10000 do local dump = my_filter(my_sinewave()) end
		for i = 1,2000 do a[i] = my_filter(my_sinewave()) end
		amps[order] = rms(a)
		if frequency == 1000 then
			ok(eq(amps[order],0.7071,0.007), 'butterworth '..tostring(order)..
			  ' gain at 1000Hz was '..tostring(amps[order]))
		end
	end
	plotfile:write(string.format("%d %g %g %g %g %g %g %g\n",
	  frequency, amps[1],amps[2],amps[3],amps[4],amps[5],amps[6],amps[7]
	))
end
plotfile:close()
local gp = assert(io.open('/tmp/butterworth_lp.gp', 'w'))
gp:write([[
set terminal jpeg enhanced size 950,505 font "sans, 16"
set colorsequence classic
set output "/tmp/butterworth_lp.jpg"
set xlabel "Cutoff frequency ]]..tostring(cutoff_freq)..[["
set ylabel "Butterworth  Lowpasses"
set logscale y
set yr [0.1:1.0]
set logscale x
set xr [100:10000]
plot \
 "/tmp/butterworth_lp.plot" using 1:2 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_lp.plot" using 1:3 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_lp.plot" using 1:4 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_lp.plot" using 1:5 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_lp.plot" using 1:6 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_lp.plot" using 1:7 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_lp.plot" using 1:8 w l axes x1y2 smooth bezier
]])
gp:close()
os.execute("gnuplot /tmp/butterworth_lp.gp")
os.execute("display /tmp/butterworth_lp.jpg &")


------------------------------------------ butterworth_hp
local samplerate  = 44100
local cutoff_freq = 1000
local my_testsine = new_sinewave(cutoff_freq,samplerate)
local plotfile = assert(io.open('/tmp/butterworth_hp.plot', 'w'))
for ifreq,frequency in ipairs(frequencies) do
	local a = {}
	local amps = {}
	for i = 1,2000 do a[#a+1] = my_testsine() end
	for order = 1,7 do
		local my_sinewave  = new_sinewave(frequency,samplerate)
		local my_filter = DF.new_digitalfilter ({
			['type']        = 'butterworth',
			['shape']       = 'highpass',
			['order']       = order,
       		['freq']        = cutoff_freq,
      		['samplerate']  = samplerate,
		})
		for i = 1,10000 do local dump = my_filter(my_sinewave()) end
		for i = 1,2000 do a[i] = my_filter(my_sinewave()) end
		amps[order] = rms(a)
	end
	plotfile:write(string.format("%d %g %g %g %g %g %g %g\n",
	  frequency, amps[1],amps[2],amps[3],amps[4],amps[5],amps[6],amps[7]
	))
end
plotfile:close()
local gp = assert(io.open('/tmp/butterworth_hp.gp', 'w'))
gp:write([[
set terminal jpeg enhanced size 950,505 font "sans, 16"
set colorsequence classic
set output "/tmp/butterworth_hp.jpg"
set xlabel "Cutoff frequency ]]..tostring(cutoff_freq)..[["
set ylabel "Butterworth  Highpasses"
set logscale y
set yr [0.1:1.0]
set logscale x
set xr [100:10000]
plot \
 "/tmp/butterworth_hp.plot" using 1:2 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_hp.plot" using 1:3 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_hp.plot" using 1:4 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_hp.plot" using 1:5 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_hp.plot" using 1:6 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_hp.plot" using 1:7 w l axes x1y2 smooth bezier, \
 "/tmp/butterworth_hp.plot" using 1:8 w l axes x1y2 smooth bezier
]])
gp:close()
os.execute("gnuplot /tmp/butterworth_hp.gp")
os.execute("display /tmp/butterworth_hp.jpg &")


-- os.exit()

------------------------------------------ bessel_lp
local samplerate  = 44100
local cutoff_freq = 1000
local my_testsine = new_sinewave(cutoff_freq,samplerate)
local plotfile = assert(io.open('/tmp/bessel_lp.plot', 'w'))
for ifreq,frequency in ipairs(frequencies) do
	local a = {}
	local amps = {}
	for i = 1,2000 do a[#a+1] = my_testsine() end
	for order = 1,7 do
		local my_sinewave  = new_sinewave(frequency,samplerate)
		local my_filter = DF.new_digitalfilter ({
			['type']        = 'bessel',
			['shape']       = 'lowpass',
			['order']       = order,
       		['freq']        = cutoff_freq,
      		['samplerate']  = samplerate,
			-- ['debug']       = true
		})
		for i = 1,10000 do local dump = my_filter(my_sinewave()) end
		for i = 1,2000 do a[i] = my_filter(my_sinewave()) end
		amps[order] = rms(a)
		if frequency == 1000 then
			ok(eq(amps[order],0.7071,0.007), 'bessel '..tostring(order)..
			  ' gain at 1000Hz was '..tostring(amps[order]))
		end
	end
	--plotfile:write(string.format("%d %g %g\n", frequency, amps[1], amps[2]))
	plotfile:write(string.format("%d %g %g %g %g %g %g %g\n",
	  frequency, amps[1],amps[2],amps[3],amps[4],amps[5],amps[6],amps[7] ))
end
plotfile:close()
local gp = assert(io.open('/tmp/bessel_lp.gp', 'w'))
gp:write([[
set terminal jpeg enhanced size 950,505 font "sans, 16"
set colorsequence classic
set output "/tmp/bessel_lp.jpg"
set xlabel "Cutoff frequency ]]..tostring(cutoff_freq)..[["
set ylabel "Bessel  Lowpasses"
set logscale y
set yr [0.01:1.0]
set logscale x
set xr [100:10000]
plot \
 "/tmp/bessel_lp.plot" using 1:2 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_lp.plot" using 1:3 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_lp.plot" using 1:4 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_lp.plot" using 1:5 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_lp.plot" using 1:6 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_lp.plot" using 1:7 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_lp.plot" using 1:8 w l axes x1y2 smooth bezier
]])
gp:close()
os.execute("gnuplot /tmp/bessel_lp.gp")
os.execute("display /tmp/bessel_lp.jpg &")

------------------------------------------ bessel_hp
local samplerate  = 44100
local cutoff_freq = 1000
local my_testsine = new_sinewave(cutoff_freq,samplerate)
local plotfile = assert(io.open('/tmp/bessel_hp.plot', 'w'))
for ifreq,frequency in ipairs(frequencies) do
	local a = {}
	local amps = {}
	for i = 1,2000 do a[#a+1] = my_testsine() end
	for order = 1,7 do
		local my_sinewave  = new_sinewave(frequency,samplerate)
		local my_filter = DF.new_digitalfilter ({
			['type']        = 'bessel',
			['shape']       = 'highpass',
			['order']       = order,
       		['freq']        = cutoff_freq,
      		['samplerate']  = samplerate,
			-- ['debug']       = true
		})
		for i = 1,10000 do local dump = my_filter(my_sinewave()) end
		for i = 1,2000 do a[i] = my_filter(my_sinewave()) end
		amps[order] = rms(a)
	end
	plotfile:write(string.format("%d %g %g %g %g %g %g %g\n",
	  frequency, amps[1],amps[2],amps[3],amps[4],amps[5],amps[6],amps[7]
	))
end
plotfile:close()
local gp = assert(io.open('/tmp/bessel_hp.gp', 'w'))
gp:write([[
set terminal jpeg enhanced size 950,505 font "sans, 16"
set colorsequence classic
set output "/tmp/bessel_hp.jpg"
set xlabel "Cutoff frequency ]]..tostring(cutoff_freq)..[["
set ylabel "Bessel  Highpasses"
set logscale y
set yr [0.01:1.0]
set logscale x
set xr [100:10000]
plot \
 "/tmp/bessel_hp.plot" using 1:2 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_hp.plot" using 1:3 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_hp.plot" using 1:4 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_hp.plot" using 1:5 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_hp.plot" using 1:6 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_hp.plot" using 1:7 w l axes x1y2 smooth bezier, \
 "/tmp/bessel_hp.plot" using 1:8 w l axes x1y2 smooth bezier
]])
gp:close()
os.execute("gnuplot /tmp/bessel_hp.gp")
os.execute("display /tmp/bessel_hp.jpg &")

os.exit()

