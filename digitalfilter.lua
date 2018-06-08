---------------------------------------------------------------------
--     This Lua5 module is Copyright (c) 2017, Peter J Billam      --
--                       www.pjb.com.au                            --
--  This module is free software; you can redistribute it and/or   --
--         modify it under the same terms as Lua5 itself.          --
---------------------------------------------------------------------
-- Example usage:
-- local MM = require 'mymodule'
-- MM.foo()

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



-- 1) from polepair to b0b1b2
-- 2) from freq,samplerate to k
-- 3) from a0a1a2b0b1b2, k to A0A1A2B0B1B2   p.56
-- 4) normalise A0A1A2B0B1B2 so that A0+A1+A2=B0+B1+B2
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

local function digi_firstorder (u, a0,a1,b1)
	-- "Introduction to Digital Filtering" Bognor and Constantinides pp.34-38
	-- z^{-1} = -j \omega T    compare [3.6] and [3.4] p.38
	local v = {}
	local u_km1 = 0.0
	local v_km1 = 0.0
	for k,u_k in ipairs(u) do
		-- v[k] = u[k]*one_minus_b1 + prev*b1
		-- v[k] = x / (1.0 + prev*b1)
		v[k] = a0*u_k + a1*u_km1 - b1*v_km1
		u_km1 = u_k
		v_km1 = v[k]
	end
	return v
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

local function zm1_pole_pair_to_b012 (x,y)   -- beta1, beta2 = x+y, x-y
	-- (1 - x*zm1 - j*y*zm1) * (1 - x*zm1 + j*y*zm1)  [3.4] pp.36,37
	-- return {[0]=1.0 ; 0, 1.0/(y*y)}
	return 1.0,  0,  x*x + y*y
end
local function freq_pair_to_a012b12 (u,v)   -- frequency omega = u +-jv
	-- Daniels p.16 Moschytz p.104 Temes/Mitra p. 337
	-- Single-Pole Denominator = (s-u - j0)
	-- Pole-Pair Denominator = (s-u - jv)*(s-u + jv) = s^2 -2us +u^2 + v^2
	--  = u^2+v^2 -2us + s^2
	--  = (u^2+v^2) * (1 - 2*u*s/(u^2+v^2) + s^2/(u^2+v^2))    since b0==1
	-- simply to convert a pole pair to b012
	if v == 0 then   -- single pole
		return 1,0,0, -1*u, 0      -- XXX 20170720 ?
	else   -- pole-pair
		return 1,0,0, -2*u/(u*u+v*v), u*u+v*v  -- XXX is this backwards ?
	end
end

-- these three only apply to lowpasses ! see Constantinides p. 56 !
local function omega_T_to_k (omega_c, T)  -- Constantinides [4.8] p.50, and p.68
	local x = omega_c * T / 2
	local s = math.sin(x) ; local c = math.cos(x)
	return c/s
end
local function freq_T_to_k (freq, T)  -- Constantinides [4.8] p.50, and p.68
	local x = math.pi * freq * T
	local s = math.sin(x) ; local c = math.cos(x)
	return c/s
end
local function freq_samplerate_to_k (freq, samplerate)  -- [4.8] p.50, and p.68
	local x = math.pi * freq / samplerate
	local s = math.sin(x) ; local c = math.cos(x)
	return c/s
end

local freq_poles = {
	-- u,v,u,v,u,v,...  non-zero imaginary part v means a pole-pair u +-jv
	-- Active Filter Design Handbook, Moschytz and Horn, 1981, Wiley, p.130
	-- Modern Low-Pass Filter Characteristics, Eggen and McAllister,
	--    Electro-Technology, August 1966
	-- Could also calculate the Butterworth poles. see Daniels [2.25] p.16
	['butterworth'] = {
		[1] = {-1.0, 0},
		[2] = {-0.70710678, 0.70710678},
		[3] = {-1.0, 0 ;  -0.5000, 0.8660},
		[4] = {-0.92388, 0.38268 ; -0.38268, 0.92388},
		[5] = {-1.0, 0 ;  -0.8090, 0.5878 ;  -0.3090, 0.9511},
		[6] = {-0.9659, 0.2588 ;  -0.70710678, 0.70710678 ;  -0.2588, 0.9659},
		[7] = {-1.0, 0 ;  -.9010, .4339 ;  -.6235, .7818 ;  -.2225, .9749},
	-- for chebyschev as a function of ripple see Moschytz and Horn pp.138-140
	},
	-- could calculate bessel poles, see Moschytz p.147, Daniels pp.249-289
	-- www.analog.com/media/en/training-seminars/design-handbooks/
	-- www.crbond.com/papers/bsf.pdf
	-- https://en.wikipedia.org/wiki/Bessel_function
	['bessel'] = {   -- https://en.wikipedia.org/wiki/Bessel_polynomials
	--	[1] = {-1.0, 0},        -- where did I get these numbers from ?
	--	[2] = {-1.1016, 0.6364},
	--	[3] = {-1.3226, 0 ;  -1.0474, 0.9992},
	--	[4] = {-1.3700, 0.4102 ; -0.9952, 1.25718},
	--	[5] = {-1.5023, 0 ;  -1.3808, 0.7179 ;  -0.9576, 1.4711},
	--	[6] = {-1.5716, 0.3209 ;  -1.3819, 0.9715 ;  -0.9307, 1.6620},
	--	[7] = {-1.6827, 0;  -1.6104, .5886;  -1.3775, 1.1904;  -.9089, 1.9749},
		[1] = {-1.0, 0},       -- see ~/html/filter/Chapter8.pdf  p.52
		[2] = {-1.1050, 0.6368},
		[3] = {-1.3270, 0 ;  -1.0509, 1.0025},
		[4] = {-1.3596, 0.4071 ; -0.9877, 1.2476},
		[5] = {-1.5069, 0 ;  -1.3851, 0.7201 ;  -0.9606, 1.4756},
		[6] = {-1.5735, 0.3213 ;  -1.3836, 0.9727 ;  -0.9318, 1.6640},
		[7] = {-1.6853, 0;  -1.6130, .5896;  -1.3797, 1.1923;  -.9104, 1.8375},
		-- also up to order 10 ...
	}
}
local function freq_pole_pair (filtertype, order, i)
	return freq_poles[filtertype][order][i+i-1],
	       freq_poles[filtertype][order][i+i]
	-- but see the bit in new_digitalfilter()
end

local function freq_a012b12_to_zm1_A012B012 (a0,a1,a2, b1,b2, option)  -- XXX
	-- a0a1a2b1b2 are for or a Frequency-Normalised Lowpass (so usually a0=1)
	-- a H(s)-to-G(z) converter, a closure.  See pp.56,58,59
    -- it needs options shape,freq,samplerate
	-- what is Constantinides p. 72 omega_c ?? beta ??
	local freq       = option['freq']
	local samplerate = option['samplerate']
	local b0 = 1.0
	local A0, A1, A2, B0, B1, B2
	if option['shape'] == 'lowpass' then
		if freq >= samplerate/2 then return 1,0,0, 1,0,0 end  -- ???
		-- s == k*(1-zm1)/(1+zm1)  where k = Omega_c*cot(omega_c*T/2)  REF??
		local tmp = math.pi * freq / samplerate
		local si = math.sin(tmp) ; local co = math.cos(tmp)
		local k = co/si -- Constantinides p. 56
		-- Constantinides p. 72 omega_c ?? beta ??
		-- (a0 + a1*s + a2*s^2) / (1 + b1*s + b2*s^2)
		-- where s becomes k*(1-zm1)/(1+zm1)
		-- multiplying numerator and denominator by (1+zm1)^2
		-- numerator   = a0*(1+2xm1+xm2) + a1*k*(1-xm2) + a2*k^2*(1-2xm1+xm2) 
		-- denominator = b0*(1+2xm1+xm2) + b1*k*(1-xm2) + b2*k^2*(1-2xm1+xm2) 
		A0 = a0 + a1*k + a2*k*k
		A1 = 2*a0 - 2*a2*k*k
		A2 = a0 - a1*k +a2*k*k
		B0 = b0 + b1*k + b2*k*k
		B1 = 2*b0 - 2*b2*k*k
		B2 = b0 - b1*k + b2*k*k
	elseif option['shape'] == 'highpass' then
		if freq >= samplerate/2 then
			return 1,0,0, 1,0,0
		end
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
	if option['debug'] then
		print('freq_a012b12_to_zm1_A012B012: (A0+A1+A2)/(B0+B1+B2) =',
	 	  (A0+A1+A2)/(B0+B1+B2) )
	end
	return A0, A1, A2, B0, B1, B2
end

function M.new_filter_section (freq_pole_re, freq_pole_im, option)
	-- We have a naming conflict here, with u,v being used
	-- 1) to mean re,im in the frequency-plane (x,y are used for zm1-plane)
	-- 2) to mean input and output of the digital-filter   :-(
	-- "Introduction to Digital Filtering" Bognor/Constantinides pp.34-40
	-- see pp.58-59 ! the numerator of G(z) is not the same as of H(s) !
	-- require 'cmath' ?  https://github.com/gregfjohnson/cmath
	-- http://stevedonovan.github.io/Penlight/packages/lcomplex.html is 404 :-(
	local a0,a1,a2,b1,b2 = freq_pair_to_a012b12(freq_pole_re, freq_pole_im)
	local A0,A1,A2,B0,B1,B2 = freq_a012b12_to_zm1_A012B012(
	  a0,a1,a2,b1,b2,option)
	if option['debug'] then
		print('new_filter_section: freq_pole_re =',freq_pole_re,
		  'freq_pole_im =',freq_pole_im)
		warn(' a012b12:  ',a0,' ',a1,' ',a2,'  ',b1,' ',b2)
		warn(' A012B012: ',A0,' ',A1,' ',A2,'  ',B0,' ',B1,' ',B2)
		warn(' (A0+A1+A2-B1-B2)/B0 = ',(A0+A1+A2-B1-B2)/B0)
	end
	local u_km1 = 0.0
	local u_km2 = 0.0
	local v_km1 = 0.0
	local v_km2 = 0.0
	return function (u_k)   -- Eqn. [3.3]  Constantinides p. 35
		-- according to Temes/Mitra p.512 and Daniels p.363,  B0=1 and A2=0
		-- but that doesn't fit with Constantinides pp.54,56 :-(
		-- local v_k = A0*u_k+A1*u_km1+A2*u_km2 - B1*v_km1-B2*v_km2   NO
		-- local v_k = (A0*u_k+A1*u_km1+A2*u_km2)/(1 + B1*v_km1-B2*v_km2) NO
		-- local v_k = (A0*u_k+A1*u_km1+A2*u_km2)/(B0 + B1*v_km1-B2*v_km2) NO
		-- which doesn't fit with the renormalisation see RENORM above
		-- Constantinides p.35 ; what happens to B0 ?
		-- v_k = (A0*u_k+A1*u_km1+A2*u_km2) / (B0*v_k + B1*v_km1-B2*v_km2)
		-- v_k*(1+B0) + B1*v_km1-B2*v_km2 = A0*u_k+A1*u_km1+A2*u_km2
		--    v_k = (A0*u_k+A1*u_km1+A2*u_km2 - B1*v_km1-B2*v_km2)/(1+B0) NO
		local v_k = (A0*u_k+A1*u_km1+A2*u_km2 - B1*v_km1-B2*v_km2)/B0  -- YES
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
	local denominator_poles   -- {u,v,u,v,u,v,u,v ...}
	-- This bit should go into freq_pole_pair()  XXX
	if string.find(option['type'], 't?chebyschev$') then
		if option['ripple'] then option['ripple'] = 1.0 end -- ripple
		if type(option['ripple']) ~= 'number' then
			return nil,"new_digitalfilter: option['ripple'] must be a number"
		end
		denominator_poles = freq_pole_pair('butterworth',option['order'])
		-- now adjust the real part
		-- see Moschytz pp.138-140, also Daniels pp.36-40, Temes pp.41-45
		-- XXX
	else
		if not freq_poles[option['type']][option['order']] then
			return nil, 'new_digitalfilter: unknown type '..option['type']
			-- or of course unsupported order ...
		end
		local i_section = 1   -- put together a chain of filter_sections XXX
		local sections  = {}  -- array of functions
		while true do
			local freq_pole_re, freq_pole_im =
			   freq_pole_pair(option['type'], option['order'], i_section)
			if not freq_pole_im then break end
			sections[i_section] =
			   M.new_filter_section (freq_pole_re, freq_pole_im, option)
			i_section = i_section + 1
		end
		return function (signal)   -- executes the chain of filter_sections
			for i, section in ipairs(sections) do
				-- print('signal =',signal)
				signal = sections[i](signal)
			end
			return signal
		end
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

To quote
https://en.wikipedia.org/wiki/Digital_filter
; I<The design of digital filters is a deceptively complex topic.[1] Although
filters are easily understood and calculated, the practical challenges
of their design and implementation are significant and are the subject
of much advanced research.>

In the literature I have, the notation is often confusing.
For example, in Temes/Mitra p.152 the general zm1 transfer-function is
given with parameters A_2 in the numerator equal to zero.

=head1 FUNCTIONS

=over 3

=item I<ttest(a,b, hypothesis)>

The arguments I<a> and I<b> are arrays of numbers

The I<hypothesis> can be one of 'a>b', 'a<b', 'b>a', 'b<a',
'a~=b' or 'a<b'.

I<ttest> returns the probability of your hypothesis being wrong.

=back

=head1 DOWNLOAD

This module is available at
http://www.pjb.com.au/comp/lua/digitalfilter.html

=head1 AUTHOR

Peter J Billam, http://www.pjb.com.au/comp/contact.html

=head1 SEE ALSO

 "Introduction to Digital Filtering", R.E.Bogner and A.G.Constantinides, Wiley 1975
 https://en.wikipedia.org/wiki/Digital_filter
 http://www.pjb.com.au/


=cut

]=]

