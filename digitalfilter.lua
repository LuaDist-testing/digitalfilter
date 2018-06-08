---------------------------------------------------------------------
--     This Lua5 module is Copyright (c) 2017, Peter J Billam      --
--                       www.pjb.com.au                            --
--  This module is free software; you can redistribute it and/or   --
--         modify it under the same terms as Lua5 itself.          --
---------------------------------------------------------------------
-- This version of digitalfilter.lua is an attempt to use the procedure
-- given in Rorabaugh's "Digital Filter Designer's Handbook", pp.287-291.

local M = {} -- public interface
M.Version = '1.0'
M.VersionDate = '17jul2017'

------------------------------ private ------------------------------
local function warn(...)
    local a = {}
    for k,v in pairs{...} do table.insert(a, tostring(v)) end
    io.stderr:write(table.concat(a),'\n') ; io.stderr:flush()
end
local function die(...) warn(...);  os.exit(1) end
local function qw(s)  -- t = qw[[ foo  bar  baz ]]
    local t = {} ; for x in s:gmatch("%S+") do t[#t+1] = x end ; return t
end

-- Constantinides' procedure is
-- 1) from polepair to b0b1b2
-- 2) from freq,samplerate to k
-- 3) from a0a1a2b0b1b2, k to A0A1A2B0B1B2   p.56
-- 4) normalise A0A1A2B0B1B2 so that B0 = 1

-- ~/html/electronics/digital_filter_designers_handbook_1.pdf
-- Rorabaugh's procedure (p.289) is:
-- In freq_sections(options)  returns { {a012b012}, {a012b012} ... }
--   1) get pole and zero pairs of butterworth, chebyschev ... etc
--   2) transform to lowpass, highpass, bandpass, bandstop  Daniels p.86
--   3) from the normalised section to the frequency-scaled section
-- In freq_section_to_zm1_section(a012b012, options)  returns A012B012:
--   4) obtain the z poles using z_{pn} = (2 + p_n*T)/(2 - p_n*T)
--   5) obtain the z zeros using z_{zn} = (2 + q_n*T)/(2 - q_n*T)
--   6) form the transfer function H(z) as in Eqn. [15.5]
-- In new_digitalfilter():
--   7) do the filter using the 1st equation on p.156
-- could also do the simple moving-average lowpass on p133
-- and a simple delay filter, much cleaner than bessel...

local function round(x) return math.floor(x+0.5) end
local function dump(x)
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

-- Useful for mapping poles in the p=u+jv plane to the zm1=x+jy plane
-- these two could be the same function ! z=(1-p)/1+z) means p=(1-z)/(1+z)
local function freq_plane_to_zm1_plane (u,v)
	--  p = u + jv     zm1 = x + jy   z = (1-p)/1+p)   from [5.12] pp.66,67
	--  p has to be present to a pair u+jv  and  u-jv
	--  we could try all combinations and not return the unstable ones...
	local denom = (1+u)^2 + v^2
	if denom == 0 then return -1, math.huge ; end   -- defend against -1,0
	local x = (1 - (u^2 + v^2)) / denom
	local y = -2*v / denom
	return x, y
end

local function zm1_plane_to_freq_plane (x,y)
	-- zm1 = x + jy     p = u + jv    p = (1-z)/(1+z)   [5.12] pp.66,67
	local denom = (1+x)^2 + y^2
	local u = (1 - (x^2 + y^2)) / denom
	local v = -2*y / denom
	return u, v
end

local function freq_pair_to_a012b12 (u,v)   -- frequency omega = u +-jv
	-- Daniels p.16 Moschytz p.104 Temes/Mitra p. 337
	-- Single-Pole Denominator = (s-u - j0)
	-- Pole-Pair Denominator = (s-u - jv)*(s-u + jv) = s^2 -2us +u^2 + v^2
	--  = u^2+v^2 -2us + s^2
	--  = (u^2+v^2) * (1 - 2*u*s/(u^2+v^2) + s^2/(u^2+v^2))    since b0==1
	-- simply to convert a pole pair to b012
	if v == 0 then   -- single pole  see Moschytz p.116 Eqn. [7.5a]
		return 1,0,0, -1*u, 0
	else   -- pole-pair
		return 1,0,0, -2*u/(u*u+v*v), u*u+v*v
	end
end

local freq_poles = {
-- SHOULD BE noralised_freq_poles(option)
-- SHOULD normalise frequency so -3dB at unity freq
-- Calculate Butterworth:  Daniels [2.25] p.16, Rorabaugh p.65 [3.2]
-- Calculate Bessel: Moschytz p.147, Daniels pp.249-289 Rorabaugh p.110,113
-- Chebyschev as function of ripple: Moschytz pp.138-140 Rorabaugh p.80
-- SEE Rorabaugh p.50 and for Laguerre's method to factorise Bessels pp.62-3

	-- u,v,u,v,u,v,...  non-zero imaginary part v means a pole-pair u +-jv
	-- Active Filter Design Handbook, Moschytz and Horn, 1981, Wiley, p.130
	-- Modern Low-Pass Filter Characteristics, Eggen and McAllister,
	--    Electro-Technology, August 1966
	['butterworth'] = {
		[1] = {-1.0, 0},
		[2] = {-0.70710678, 0.70710678},
		[3] = {-1.0, 0 ;  -0.5000, 0.8660},
		[4] = {-0.92388, 0.38268 ; -0.38268, 0.92388},
		[5] = {-1.0, 0 ;  -0.8090, 0.5878 ;  -0.3090, 0.9511},
		[6] = {-0.9659, 0.2588 ;  -0.70710678, 0.70710678 ;  -0.2588, 0.9659},
		[7] = {-1.0, 0 ;  -.9010, .4339 ;  -.6235, .7818 ;  -.2225, .9749},
	},
	-- www.analog.com/media/en/training-seminars/design-handbooks/
	-- www.crbond.com/papers/bsf.pdf
	-- https://en.wikipedia.org/wiki/Bessel_function
	['bessel'] = {   -- https://en.wikipedia.org/wiki/Bessel_polynomials
	--	[1] = {-1.0, 0},        -- see Moschytz p.130
	--	[2] = {-1.1016, 0.6364},
	--	[3] = {-1.3226, 0 ;  -1.0474, 0.9992},
	--	[4] = {-1.3700, 0.4102 ; -0.9952, 1.25718},
	--	[5] = {-1.5023, 0 ;  -1.3808, 0.7179 ;  -0.9576, 1.4711},
	--	[6] = {-1.5716, 0.3209 ;  -1.3819, 0.9715 ;  -0.9307, 1.6620},
	--	[7] = {-1.6827, 0;  -1.6104, .5886;  -1.3775, 1.1904;  -.9089, 1.9749},
		[1] = {-1.0, 0},       -- see ~/html/filter/Chapter8.pdf  p.52
	--	[2] = {-1.1050, 0.6368},
		[2] = {-0.9318, 1.6640},
		[3] = {-1.3270, 0 ;  -1.0509, 1.0025},
		[4] = {-1.3596, 0.4071 ; -0.9877, 1.2476},
		[5] = {-1.5069, 0 ;  -1.3851, 0.7201 ;  -0.9606, 1.4756},
		[6] = {-1.5735, 0.3213 ;  -1.3836, 0.9727 ;  -0.9318, 1.6640},
		[7] = {-1.6853, 0;  -1.6130, .5896;  -1.3797, 1.1923;  -.9104, 1.8375},
		-- also up to order 10 ...
	}
}
function M.freq_pole_pair (filtertype, order, i)
	return freq_poles[filtertype][order][i+i-1],
	       freq_poles[filtertype][order][i+i]
	-- This bit should go into M.freq_pole_pair()  XXX
	-- if string.find(option['type'], 't?chebyschev$') then
	-- 	if option['ripple'] then option['ripple'] = 1.0 end -- ripple
	-- 	if type(option['ripple']) ~= 'number' then
	-- 		return nil,"new_digitalfilter: option['ripple'] must be a number"
	-- 	end
	-- local denominator_poles   -- {u,v,u,v,u,v,u,v ...}
	-- 	denominator_poles = M.freq_pole_pair('butterworth',option['order'])
		-- now adjust the real part
		-- see Moschytz pp.138-140, also Daniels pp.36-40, Temes pp.41-45
		-- XXX
	-- else
end

function M.pole_pair_to_freq_Q (u,v)   -- poles at (u+jv)*(u-jv) = u^2+v^2
	-- pole-pair u +-jv  so  denominator is (s -u-jv)*(s -u+jv)
	-- = u^2+v^2 -2*u*s + s^2 so, by Temes/Mitra p.337
	local freq  = math.sqrt(u*u + v*v)
	local Q     = freq / (-2 * u)
	return freq, Q
end

function M.b0b1b2_to_freq_Q (b0,b1,b2)   -- Temes/Mitra p.337
	local omega = math.sqrt(b0/b2)
	local Q     = omega/(b1/b2)
	return 0.5*omega/math.pi, Q
end

function M.freq_sections (option)
-- freq_sections(option)  returns { {a012b012}, {a012b012} ... }
--   1) get normalised pole and zero pairs of butterworth, chebyschev ... etc
--   2) transform to lowpass, highpass, bandpass, bandstop  Daniels p.86
--   3) from the normalised section to the frequency-scaled section
	if not freq_poles[option['type']] then
		return nil, 'freq_sections: unknown type '..option['type']
	end
	if not freq_poles[option['type']][option['order']] then
		return nil, 'freq_sections: unimplemented order '..option['order']
	end
	if option['freq'] >= option['samplerate']/2 then
		if  option['shape']=='lowpass' or option['shape']=='bandpass' then
			return { {0, 0, 0,  1, 0, 0} }
		elseif option['shape']=='highpass' or option['shape']=='bandstop' then
			return { {1, 0, 0,  1, 0, 0} }
		end
	end
	local normalised_poles = freq_poles[option['type']][option['order']]
	local sections = {}
	for i = 1, #normalised_poles, 2 do
		local re = normalised_poles[i]
		local im = normalised_poles[i+1]
		local a0,a1,a2, b0,b1,b2
		if im == 0 then   -- a single-pole section
			if option['shape'] == 'bandpass' then
				return nil, 'freq_sections: bandpass order must be even'
			elseif option['shape'] == 'bandstop' then
				return nil, 'freq_sections: bandstop order must be even'
			end
			a0=1; a1=0; a2=0; b0=1; b1=-1*re; b2=0
		else  -- a conjugate pair of poles
			if option['shape'] == 'bandpass' then -- Temes/Mitra p.343 [8.31]
				a0=0; a1=1; a2=0; b0=1; b1=1/option['Q']; b2=1
			elseif option['shape'] == 'bandstop' then
				a0=1; a1=0; a2=1; b0=1; b1=1/option['Q']; b2=1
			else
				a0=1; a1=0; a2=0; b0=1; b1=-2*re/(re*re+im*im); b2=re*re+im*im
			end
		end
		-- transform to the desired shape and unnormalise, Daniels pp.86-89
		local omega = 2 * math.pi * option['freq']
		if option['shape'] == 'highpass' then
			local tmp
			tmp = a2; a2 = a0; a0 = tmp
			tmp = b2; b2 = b0; b0 = tmp
		end
		-- 20170727 denormalise AFTER highpass-exchanging a0,a2 and b0,b2
		a1 = a1 / omega;  a2 = a2 / (omega*omega)
		b1 = b1 / omega;  b2 = b2 / (omega*omega)
		table.insert(sections, {a0,a1,a2, b0,b1,b2})
-- print(M.b0b1b2_to_freq_Q (b0,b1,b2))
	end
	return sections
end

function M.factorise(b0,b1,b2)   -- just factorises a quadratic section
	if b2 == 0 then
		-- if b1 == 0 then return 0,b0
		return b1, b0
	else
		-- This throws away a gain factor, so will need later normalisation ..
		-- (s - u-j*v)*(s - u+j*v) = s^2 -2*s*u + v^2
		-- scaling up by b2:   b2=b2,    b1=b2*-2*u,   b0=b2*v^2
		-- u = -0.5*b1/b2      v = sqrt(b0/b2)
		return -0.5*b1/b2 , math.sqrt(b0/b2)
		-- return -0.5*b1/math.sqrt(b2) , math.sqrt(b0)
	end
end

local function freq_a012b012_to_zm1_A012B012 (a012b012, option)
	-- see Rorabaugh pp.287 (see also pp.289-291)
	-- s --> (2/T) * (1 - zm1) / (1 + zm1)
	-- so:   b0      + b1*s                     + b2*s^2
	--> b0*(1+zm1)^2 + b1*(2/T)*(1+zm1)*(1-zm1) + b2*(2/T)^2*(1-zm1)^2
	--> B0 = b0 + b1*(2/T) + b2*(2/T)^2
	--> B1 = 2*b0 - 2*b2*(2/T)^2
	--> B2 = b0 - b1*(2/T) + b2*(2/T)^2
	--> 2/T = 2*samplerate    (? or pi* ? )
	local a0,a1,a2, b0,b1,b2 = table.unpack(a012b012)
	local two_over_T = 2*option['samplerate']
	local two_over_T_squared = two_over_T^2
	local A0 = a0 + a1*two_over_T + a2*two_over_T_squared
	local A1 = 2*a0 - 2*a2*two_over_T_squared
	local A2 = a0 - a1*two_over_T + a2*two_over_T_squared
	local B0 = b0 + b1*two_over_T + b2*two_over_T_squared
	local B1 = 2*b0 - 2*b2*two_over_T_squared
	local B2 = b0 - b1*two_over_T + b2*two_over_T_squared
	return {A0,A1,A2, B0,B1,B2}
end

--[==[
local function freq_a012b012_to_zm1_A012B012 (a0,a1,a2, b0,b1,b2, option)
	-- see Rorabaugh pp.287-289 (or pp.289-291)
	-- but it's easier if I work directly from the poles and zeros !
	-- local freq       = option['freq']
	-- local samplerate = option['samplerate']
	local A0, A1, A2, B0, B1, B2
	-- 1) Find the new poles: z_{pn} = (2 + p_n*T)/(2 - p_n*T)
	-- 2) Find the new zeros: z_{zn} = (2 - q_n*T)/(2 + q_n*T)
	-- 3) H(z) = H_0 * 
	if option['shape'] == 'lowpass' then
		if freq >= samplerate/2 then return 1,0,0, 1,0,0 end
		-- s == k*(1-zm1)/(1+zm1)  where k = Omega_c*cot(omega_c*T/2)  p.56
		-- Rorabaugh calls this "Bilinear Transfromation" but swaps a and b
		-- see Constantinides p.56; or k = 2/T Rorabaugh p.287
		local tmp = math.pi * freq / samplerate
		local si = math.sin(tmp) ; local co = math.cos(tmp)
		local k = co/si -- Constantinides p. 56
		-- Constantinides p. 72 omega_c ?? beta ??
		-- (a0 + a1*s + a2*s^2) / (1 + b1*s + b2*s^2)
		-- where s becomes k*(1-zm1)/(1+zm1)
		-- multiplying numerator and denominator by (1+zm1)^2
		-- numerator   = a0*(1+2zm1+zm2) + a1*k*(1-zm2) + a2*k*k*(1-2zm1+zm2) 
		-- denominator = b0*(1+2zm1+zm2) + b1*k*(1-zm2) + b2*k*k*(1-2zm1+zm2) 
		A0 = a0 + a1*k + a2*k*k
		A1 = 2*a0 - 2*a2*k*k
		A2 = a0 - a1*k +a2*k*k
		B0 = b0 + b1*k + b2*k*k
		B1 = 2*b0 - 2*b2*k*k
		B2 = b0 - b1*k + b2*k*k
	elseif option['shape'] == 'highpass' then
		if freq >= samplerate/2 then return 1,0,0, 1,0,0 end
		-- s == k*(1+zm1)/(1-zm1)  where k = Omega_c*cot(omega_c*T/2)
		local tmp = math.pi * freq / samplerate
		local si = math.sin(tmp) ; local co = math.cos(tmp)
		local k = si/co  -- Constantinides p. 56
		-- (a0 + a1*s + a2*s^2) / (1 + b1*s + b2*s^2)
		-- where s becomes k*(1+zm1)/(1-zm1) 
		-- multiplying numerator and denominator by (1-zm1)^2
		-- numerator   = a0*(1-2zm1+zm2) + a1*k*(1-zm2) + a2*k^2*(1+2zm1+zm2) 
		-- denominator =   (1-2zm1+zm2)  + b1*k*(1-zm2) + b2*k^2*(1+2zm1+zm2) 
		A0 = a0 + a1*k + a2*k*k
		A1 = -2*a0 + 2*a2*k*k
		A2 = a0 - a1*k +a2*k*k
		B0 = 1  + b1*k + b2*k*k
		B1 = -2*b0 + 2*b2*k*k
		B2 = b0 - b1*k + b2*k*k
	else return nil,
		'freq_a012b12_to_zm1_A012B012: unknown shape '..option['shape']
	end
	local RENORM = (A0+A1+A2-B1-B2)/B0
	if option['debug'] then
		print('freq_a012b12_to_zm1_A012B012: (A0+A1+A2-B1-B2)/B02) =', RENORM)
		if RENORM == 0 then
			print(option['type'], option['shape'], option['order'])
			print('a012 =',a0,a1,a2,' b012 =',b0,b1,b2)
			print('A012 =',A0,A1,A2,' B012 =',B0,B1,B2)
			os.exit()
		end
	 	--  (A0+A1+A2)/(B0+B1+B2) )
	end
	-- BUT Constantinides p.36 says: G(z) = V(z)/U(z)
	-- where V(z) is the z-transform of the OUTPUT signal
	--  and  U(z) is the z-transform of the INPUT  signal :-( !?!
	-- return A0, A1, A2, B0*RENORM, B1, B2
	-- return A0, A1, A2, B0,        B1, B2
	return A0/B0, A1/B0, A2/B0, 1, B1/B0, B2/B0
end
]==]

function M.new_filter_section (A012B012, option)
	-- We have a naming conflict here, with u,v being used
	-- 1) to mean re,im in the frequency-plane (x,y are used for zm1-plane)
	-- 2) to mean input and output of the digital-filter   :-(
	-- "Introduction to Digital Filtering" Bognor/Constantinides pp.34-40
	-- see pp.58-59 ! the numerator of G(z) is not the same as of H(s) !
	-- require 'cmath' ?  https://github.com/gregfjohnson/cmath
	-- http://stevedonovan.github.io/Penlight/packages/lcomplex.html is 404 :-(

	--local a012b012 = M.freq_pair_to_a012b012(freq_pole_re,freq_pole_im)
	local A0,A1,A2,B0,B1,B2 = table.unpack(A012B012)
	if option['debug'] then
		print('new_filter_section:')
		warn(' A012B012: ',A0,' ',A1,' ',A2,'  ',B0,' ',B1,' ',B2)
		-- warn(' (A0+A1+A2-B1-B2)/B0 = ',(A0+A1+A2-B1-B2)/B0)
	end
	local u_km1 = 0.0
	local u_km2 = 0.0
	local v_km1 = 0.0
	local v_km2 = 0.0
	return function (u_k)   -- Eqn. [3.3]  Constantinides p. 35
		-- according to Temes/Mitra p.512 and Daniels p.363,  B0=1 and A2=0
		-- but that doesn't fit with Constantinides pp.54,56 :-(
		-- Constantinides p.35 ; what happens to B0 ?
		-- v_k = (A0*u_k+A1*u_km1+A2*u_km2) / (B0*v_k + B1*v_km1-B2*v_km2)
		-- v_k*(1+B0) + B1*v_km1-B2*v_km2 = A0*u_k+A1*u_km1+A2*u_km2
		-- local v_k = (A0*u_k+A1*u_km1+A2*u_km2-B1*v_km1-B2*v_km2)/(1+B0) NO
		-- local v_k = A0*u_k+A1*u_km1+A2*u_km2 - B1*v_km1-B2*v_km2 unstable
		-- see Rorabaugh p.156 top eqn, with a and b swapped or p.130 eqn 7.6
		local v_k = (A0*u_k+A1*u_km1+A2*u_km2 - B1*v_km1-B2*v_km2)/B0 -- YES
		u_km2 = u_km1 ; u_km1 = u_k
		v_km2 = v_km1 ; v_km1 = v_k
		return v_k
	end
end

------------------------------ public ------------------------------

function M.new_digitalfilter (option)
-- print('new_digitalfilter =',dump(option))
	-- this is a closure, putting together a chain of filter_sections
	if not option['type']  then option['type']  = 'butterworth' end
	if type(option['type']) ~= 'string' then
		return nil, "new_digitalfilter: option['type'] must be a string"
	end
	if not option['order'] then option['order'] = 4 end
	if type(option['order']) ~= 'number' then
		return nil, "new_digitalfilter: option['order'] must be a number"
	end
	if not option['shape'] then option['shape'] = 'lowpass' end
	if type(option['shape']) ~= 'string' then   --Constantinides p. 56
		return nil, "new_digitalfilter: option['shape'] must be a string"
	end
	local i_section = 1   -- put together a chain of filter_sections XXX
	local section_funcs  = {}  -- array of functions
	-- freq_sections(options)  returns { {a012b012}, {a012b012} ... }
	local section_a012b012s = M.freq_sections(option)
	for i, a012b012 in ipairs(section_a012b012s) do
		local A012B012=freq_a012b012_to_zm1_A012B012(a012b012,option)
		section_funcs[i] = M.new_filter_section(A012B012, option)
	end
	return function (signal)   -- executes the chain of filter_sections
		--local old_signal = signal
		for i, section in ipairs(section_funcs) do
			-- print('signal =',signal)
			signal = section_funcs[i](signal)
		--if math.abs(signal) > math.abs(old_signal) then NO
		--	print(option['type'],option['order'],' section number',i)
		--end
		end
		return signal
	end
end

return M

--[=[

=pod

=head1 NAME

digitalfilter.lua - Butterworth, Chebyschev and Bessel digital filters: 

=head1 SYNOPSIS

 local DF = require 'digitalfilter'
 local my_filter = DF.new_digitalfilter ({   --returns a closure
    ['type']        = 'butterworth',
    ['order']       = 3,
    ['shape']       = 'lowpass',
    ['freq']        = 1000,
    ['samplerate']  = 441000,
 })
 for i = 1,95 do
    local u = (math.floor((i%16)/8   + 0.01)*2 - 1)  -- square wave
    local x = my_filter(u)
    if i >= 80 then print('my_filter('..u..') \t=', x) end
 end

=head1 DESCRIPTION

This module provides some Digital Filters - Butterworth, Chebyschev and Bessel
in lowpass and highpass.
Hopefully, Inverse Chebyschev, bandpass and bandstop will follow.

To quote
https://en.wikipedia.org/wiki/Digital_filter
; "The design of digital filters is a deceptively complex topic. Although
filters are easily understood and calculated, the practical challenges
of their design and implementation are significant and are the subject
of much advanced research."

In the literature I have, the notation is often confusing.
For example, in Temes/Mitra p.152 the general zm1 transfer-function is
given with parameters A_2 in the numerator equal to zero.
Constantinides sometimes uses u and v to mean the real and imaginary
parts of the frequency omega, and sometimes to mean the input and output
signals of a digital filter.
Rorabaugh, however, (p.156) uses X(z) and Y(z) to mean the input and output
signals of a digital filter.
Rorabaugh sometimes uses q to mean the quality of filter-section,
sometimes to mean the location of a zero in the z^-1 plane.
Constantinides sometimes uses a and b to mean the coefficients of the
transfer function in the frequency-domain, and alpha and beta to mean
the coefficients of the transfer function in the z^-1-domain,
but he often uses a and b to mean
the coefficients of the transfer function in the z^-1-domain.
Or, comparing Constantinides p.36 with Rorabaugh p.156,
the meanings of a and b have been swapped, also the meanings of G(z) and H(z).

This version of I<digitalfilter.lua> is an attempt to use the procedure
given in Rorabaugh's "Digital Filter Designer's Handbook", pp.287-291.

=head1 THE TABLE OF OPTIONS

=over 3

Various functions, including I<new_digitalfilter(options)>,
need an argument to set the parameters;
This argument is a table, with keys
'type', 'order', 'shape', 'freq' and 'samplerate',
and for basspass and bandstop also 'Q'.

The 'type' can be 'butterworth', 'bessel', or 'chebyschev'.
In the case of 'chebyschev' there is an additional option 'ripple'
which specifies in decibels the desired ripple in the passband,
defaulting to 1.

The 'order' can currently be from 1 to 7 for all types,
and this range will probably be extended.

The 'shape' can be 'highpass', 'lowpass', 'bandpass' or 'bandstop',
though currently 'highpass' or 'lowpass' are only implemented
for 'order' = 2.

The 'freq' is the desired cutoff-frequency for 'lowpass' and 'highpass'
filters, and the centre-frequency for 'bandpass' and 'bandstop', 
It must be given in the same units as the 'samplerate'.
A 'freq' greater than half the 'samplerate' is a mistake,
but is implemented as setting the gain to zero for 'lowpass' or 'bandpass',
or 1 for 'highpass' or 'bandstop'.

The 'samplerate' is the sampling-frequency.
For example in audio use 'samplerate' will often be 44100 or 48000.

The 'Q' is only necessary for 'bandpass' and 'bandstop' shapes,
and specifies the I<quality> of the pole.
High 'Q' gives the filter a narrower resonance.

=back

=head1 FUNCTIONS

=over 3

=item I<my_filter = new_digitalfilter(options)>

I<new_digitalfilter> returns a closure - a function that lies
within a context of local variables which implement the filter.
You can then call this closure with your input-signal-value as argument,
and it will return the filtered-signal-value.

The argument I<options> is a table, with keys
'type', 'order', 'shape', 'freq' and 'samplerate'.

If an error is detected, I<new_digitalfilter> returns I<nil>
and an error message, so it can be used with I<assert>.

It is hoped that some future version of I<new_digitalfilter>
will return also a second closure,
allowing the 'freq' parameter to be varied during use.

=back

=head1 DOWNLOAD

This module is available at
http://www.pjb.com.au/comp/lua/digitalfilter.html

=head1 AUTHOR

Peter J Billam, http://www.pjb.com.au/comp/contact.html

=head1 CHANGES

 20170719 1.0 place-holder; not working yet
 20170722 1.1 bad bessel freq-resp, using Constantinides' book
 20170729 1.2 the same bad bessel freq-resp, using Rorabaugh's book

=head1 SEE ALSO

 "Modern Filter Theory and Design", Gabor C. Temes and Sanjit K. Mitra,
    Wiley, 1973
 "Approximation Methods for Electronic Filter Design", Richard W. Daniels,
    McGraw-Hill, 1974
 "Introduction to Digital Filtering", R.E.Bogner and A.G.Constantinides,
    Wiley 1975
 "Active Filter Design Handbook", G.S. Moschytz and Petr Horn,
    Wiley, 1981
 "Digital Filter Designer's Handbook", C. Bitton Rorabaugh,
    TAB Books (McGraw-Hill) 
 http://cdn.preterhuman.net/texts/engineering/Dsp/
 https://en.wikipedia.org/wiki/Digital_filter
 http://www.pjb.com.au/

=cut

]=]

