local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 38) then
					if (Enum <= 18) then
						if (Enum <= 8) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum == 0) then
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum == 2) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
								elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 5) then
								if (Enum == 4) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									local DIP;
									local NStk;
									local Upv;
									local List;
									local Cls;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Cls = {};
									for Idx = 1, #Lupvals do
										List = Lupvals[Idx];
										for Idz = 0, #List do
											Upv = List[Idz];
											NStk = Upv[1];
											DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 6) then
								Stk[Inst[2]] = {};
							elseif (Enum > 7) then
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							end
						elseif (Enum <= 13) then
							if (Enum <= 10) then
								if (Enum > 9) then
									Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
								else
									do
										return;
									end
								end
							elseif (Enum <= 11) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum > 12) then
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 15) then
							if (Enum == 14) then
								local B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 16) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						elseif (Enum == 17) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] < Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
						end
					elseif (Enum <= 28) then
						if (Enum <= 23) then
							if (Enum <= 20) then
								if (Enum == 19) then
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum <= 21) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							elseif (Enum == 22) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 25) then
							if (Enum == 24) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 26) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum == 27) then
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 33) then
						if (Enum <= 30) then
							if (Enum > 29) then
								Stk[Inst[2]] = Inst[3];
							else
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum <= 31) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						elseif (Enum > 32) then
							Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 35) then
						if (Enum == 34) then
							Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 36) then
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					elseif (Enum == 37) then
						local A = Inst[2];
						Stk[A] = Stk[A]();
					else
						local A;
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 58) then
					if (Enum <= 48) then
						if (Enum <= 43) then
							if (Enum <= 40) then
								if (Enum == 39) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								end
							elseif (Enum <= 41) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 42) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 45) then
							if (Enum > 44) then
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]] = Inst[3] - Stk[Inst[4]];
							end
						elseif (Enum <= 46) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						elseif (Enum > 47) then
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 53) then
						if (Enum <= 50) then
							if (Enum > 49) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 51) then
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum == 52) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 4) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							Stk[Inst[2]]();
						end
					elseif (Enum <= 55) then
						if (Enum == 54) then
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 56) then
						local B;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Stk[Inst[4]];
						if B then
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = B;
							VIP = Inst[3];
						end
					elseif (Enum > 57) then
						Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
					else
						local Edx;
						local Results;
						local A;
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Stk[A + 1])};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					end
				elseif (Enum <= 68) then
					if (Enum <= 63) then
						if (Enum <= 60) then
							if (Enum > 59) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 61) then
							if (Stk[Inst[2]] < Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 62) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						else
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 65) then
						if (Enum > 64) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 66) then
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
					elseif (Enum == 67) then
						VIP = Inst[3];
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 73) then
					if (Enum <= 70) then
						if (Enum > 69) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							local A = Inst[2];
							local Cls = {};
							for Idx = 1, #Lupvals do
								local List = Lupvals[Idx];
								for Idz = 0, #List do
									local Upv = List[Idz];
									local NStk = Upv[1];
									local DIP = Upv[2];
									if ((NStk == Stk) and (DIP >= A)) then
										Cls[DIP] = NStk[DIP];
										Upv[1] = Cls;
									end
								end
							end
						end
					elseif (Enum <= 71) then
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif (Enum == 72) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						Stk[Inst[2]] = Stk[Inst[3]] ^ Inst[4];
					end
				elseif (Enum <= 75) then
					if (Enum == 74) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					else
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
					end
				elseif (Enum <= 76) then
					do
						return Stk[Inst[2]];
					end
				elseif (Enum == 77) then
					Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
				elseif (Stk[Inst[2]] == Inst[4]) then
					VIP = VIP + 1;
				else
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!183Q0003063Q004C696E65617203043Q005175616403023Q00496E2Q033Q004F757403053Q00496E4F757403023Q005F47030C3Q0054772Q656E5365727669636503043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403053Q00426173657303063Q0043616D657261026Q001040026Q33D33F03093Q0057616C6B53702Q6564026Q00494003043Q007461736B03053Q00737061776E03023Q00554903063Q00412Q64546162030A3Q004E756B65204D65726765004F4Q00068Q0014000100014Q000600023Q000200023A00035Q0010480002000100032Q000600033Q000300023A000400013Q00104800030003000400023A000400023Q00104800030004000400023A000400033Q0010480003000500040010480002000200032Q0004000100023Q00023A000200043Q00122D000300063Q00102Q000300073Q00122Q000300083Q00202Q00030003000900122Q0005000A6Q00030005000200202Q00040003000B00122Q0005000C3Q00202Q00050005000D00122Q0007000E4Q003B00050007000200121D0006000C3Q00202Q00060006000D00122Q0008000F6Q00060008000200122Q000700103Q00122Q000800113Q00122Q000900116Q000A3Q000100302Q000A001200134Q000B00014Q0012000C5Q000634000D0005000100022Q00043Q00054Q00043Q00043Q00023A000E00063Q00023A000F00073Q00023A001000083Q00063400110009000100032Q00043Q000F4Q00043Q00104Q00043Q00043Q0006340012000A000100032Q00043Q000C4Q00043Q00044Q00043Q000A3Q0006340013000B000100012Q00043Q00063Q0006340014000C000100012Q00043Q00043Q001244001500143Q00204A0015001500150006340016000D0001000C2Q00043Q00084Q00043Q000B4Q00043Q00134Q00043Q000D4Q00043Q000E4Q00043Q00044Q00043Q000F4Q00043Q00104Q00043Q00124Q00043Q00144Q00043Q00114Q00043Q00074Q0037001500020001001244001500163Q00204A00150015001700121E001600183Q0006340017000E000100022Q00043Q000B4Q00043Q000A4Q00230015001700012Q00093Q00013Q000F7Q0001024Q004C3Q00024Q00093Q00019Q002Q0001034Q004B00016Q004C000100024Q00093Q00017Q00013Q00026Q00F03F01063Q001021000100013Q00102Q000200016Q00010001000200102Q0001000100014Q000100028Q00017Q00043Q00026Q00E03F027Q0040027Q00C0026Q00F03F010D3Q00263D3Q0006000100010004433Q00060001001022000100024Q004B000100013Q00060F0001000B000100010004433Q000B0001001022000100033Q00201000010001000200204900010001000200200700010001000200102C0001000400012Q004C000100024Q00093Q00017Q00083Q0003043Q007479706503083Q00757365726461746103053Q007063612Q6C03053Q007461626C6503013Q00780003013Q007903013Q007A011F3Q001244000100014Q000400026Q002E00010002000200264E0001000B000100020004433Q000B0001001244000100033Q00063400023Q000100012Q00048Q000B000100024Q001500015Q0004433Q001C0001001244000100014Q000400026Q002E00010002000200264E0001001C000100040004433Q001C000100204A00013Q000500261300010019000100060004433Q0019000100204A00013Q000700261300010019000100060004433Q0019000100204A00013Q000800264E0001001A000100060004433Q001A00014Q00016Q0012000100014Q004C000100024Q001200016Q004C000100024Q00093Q00013Q00013Q00033Q0003013Q007803013Q007903013Q007A000C4Q002A7Q00204A5Q000100062B3Q000A00013Q0004433Q000A00012Q002A7Q00204A5Q000200062B3Q000A00013Q0004433Q000A00012Q002A7Q00204A5Q00032Q004C3Q00024Q00093Q00017Q00043Q0003063Q00697061697273030B3Q004765744368696C6472656E03053Q007063612Q6C03063Q00557365724964001C4Q002A7Q00060F3Q0005000100010004433Q000500012Q00148Q004C3Q00023Q0012443Q00014Q000800015Q00202Q0001000100024Q000100029Q00000200044Q00170001001244000500033Q00063400063Q000100012Q00043Q00044Q002900050002000600062B0005001600013Q0004433Q001600012Q002A000700013Q00204A00070007000400063000060016000100070004433Q001600012Q004C000400024Q004500035Q0006333Q000B000100020004433Q000B00012Q00148Q004C3Q00024Q00093Q00013Q00013Q00023Q00030C3Q00476574412Q74726962757465030B3Q004F776E657255736572496400064Q00197Q00206Q000100122Q000200028Q00029Q008Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403053Q004E756B6573030B3Q004765744368696C6472656E010D3Q0006400001000500013Q0004433Q0005000100202F00013Q000100121E000300024Q003B00010003000200060F00010009000100010004433Q000900012Q000600026Q004C000200023Q00202F0002000100032Q000B000200034Q001500026Q00093Q00017Q00013Q0003053Q007063612Q6C010B3Q001244000100013Q00063400023Q000100012Q00048Q002900010002000200062B0001000800013Q0004433Q0008000100060E00030009000100020004433Q000900012Q0014000300034Q004C000300024Q00093Q00013Q00013Q00023Q00030C3Q00476574412Q7472696275746503043Q005469657200064Q00197Q00206Q000100122Q000200028Q00029Q008Q00017Q00043Q00030B3Q005072696D6172795061727403163Q0046696E6446697273744368696C64576869636849734103083Q004D6573685061727403053Q007063612Q6C01153Q00204A00013Q000100060F00010006000100010004433Q0006000100202F00013Q000200121E000300034Q003B00010003000200060F0001000A000100010004433Q000A00012Q0014000200024Q004C000200023Q001244000200043Q00063400033Q000100012Q00043Q00014Q002900020002000300062B0002001200013Q0004433Q0012000100060E00040013000100030004433Q001300012Q0014000400044Q004C000400024Q00093Q00013Q00013Q00013Q0003083Q00506F736974696F6E00044Q002A7Q00204A5Q00012Q004C3Q00024Q00093Q00017Q000E3Q0003063Q0069706169727303053Q007461626C6503063Q00696E7365727403053Q00706169727303043Q00736F7274027Q004003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E026Q00F03F03043Q006D61746803043Q006875676503093Q004D61676E6974756465015D4Q003C00015Q00122Q000200016Q00038Q00020002000400044Q001900012Q002A00076Q0026000800066Q0007000200024Q000800016Q000900066Q00080002000200062Q0007001900013Q0004433Q0019000100062B0008001900013Q0004433Q001900012Q002400090001000700060F00090013000100010004433Q001300012Q000600096Q0028000100070009001247000900023Q00202Q0009000900034Q000A000100074Q000B00066Q0009000B000100063300020005000100020004433Q000500012Q000600025Q001244000300044Q0004000400014Q00290003000200050004433Q00250001001244000700023Q00204A0007000700032Q0004000800024Q0004000900064Q002300070009000100063300030020000100010004433Q00200001001244000300023Q00204A0003000300052Q0004000400023Q00023A00056Q003900030005000100122Q000300016Q000400026Q00030002000500044Q005800012Q00240008000100072Q0032000900083Q000E3600060058000100090004433Q005800012Q002A000900023Q00204A00090009000700062B0009003D00013Q0004433Q003D00012Q002A000900023Q00204A00090009000700202F00090009000800121E000B00094Q003B0009000B0002000640000A0040000100090004433Q0040000100204A000A0009000A00204A000B0008000B001244000C000C3Q00204A000C000C000D00062B000A005400013Q0004433Q00540001001244000D00014Q0004000E00084Q0029000D0002000F0004433Q005200012Q002A001200014Q0017001300116Q0012000200024Q00130012000A00202Q00130013000E00062Q001300520001000C0004433Q005200012Q0004000C00134Q0004000B00113Q000633000D0049000100020004433Q004900012Q0004000D000B4Q0004000E00074Q0004000F00084Q003F000D00023Q00063300030030000100020004433Q003000012Q0014000300034Q004C000300024Q00093Q00013Q00017Q0002063Q00061B0001000300013Q0004433Q000300014Q00026Q0012000200014Q004C000200024Q00093Q00017Q00183Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403083Q00506F736974696F6E03073Q00566563746F72332Q033Q006E657703013Q005803013Q005903013Q005A03093Q004D61676E6974756465029A5Q99B93F03043Q006D6174682Q033Q006D6178029A5Q99A93F026Q00F03F03093Q0057616C6B53702Q656403023Q006F7303053Q00636C6F636B03053Q00636C616D70028Q0003053Q007063612Q6C03043Q007461736B03043Q007761697402FCA9F1D24D62903F015E4Q002A00015Q00062B0001000400013Q0004433Q000400012Q00093Q00014Q0012000100014Q004600016Q002A000100013Q00204A0001000100010006400002000D000100010004433Q000D000100202F00020001000200121E000400034Q003B00020004000200060F00020012000100010004433Q001200012Q001200036Q004600036Q00093Q00013Q00204A000300020004001211000400053Q00202Q00040004000600202Q00053Q000700202Q00060003000800202Q00073Q00094Q0004000700024Q00050004000300202Q00050005000A00262Q000500200001000B0004433Q002000012Q001200066Q004600066Q00093Q00013Q0012440006000C3Q00200200060006000D00122Q0007000E3Q00122Q0008000C3Q00202Q00080008000D00122Q0009000F6Q000A00023Q00202Q000A000A00104Q0008000A00024Q0008000500084Q00060008000200122Q000700113Q00202Q0007000700124Q000700010002001244000800113Q00204A0008000800122Q00250008000100022Q00420008000800070006030008005B000100060004433Q005B00012Q002A000800013Q00204A0001000800010006400002003C000100010004433Q003C000100202F00080001000200121E000A00034Q003B0008000A00022Q0004000200083Q00060F0002003F000100010004433Q003F00010004433Q005B00010012440008000C3Q00201F00080008001300122Q000900113Q00202Q0009000900124Q0009000100024Q0009000900074Q00090009000600122Q000A00143Q00122Q000B000F6Q0008000B00024Q0009000400034Q0009000900084Q00090003000900122Q000A00153Q000634000B3Q000100022Q00043Q00024Q00043Q00094Q002E000A0002000200060F000A0055000100010004433Q005500012Q004500085Q0004433Q005B0001001244000B00163Q002005000B000B001700122Q000C00186Q000B000200014Q00085Q00044Q002E00012Q001200086Q004600086Q00093Q00013Q00013Q00013Q0003083Q00506F736974696F6E00044Q002A8Q002A000100013Q0010483Q000100012Q00093Q00017Q00033Q00030E3Q0046696E6446697273744368696C64030E3Q0048656C644E756B6556697375616C03053Q007063612Q6C00164Q002A7Q00062B3Q000700013Q0004433Q000700012Q002A7Q00202F5Q000100121E000200024Q003B3Q0002000200060F3Q000B000100010004433Q000B00012Q0014000100014Q004C000100023Q001244000100033Q00063400023Q000100012Q00048Q002900010002000200062B0001001300013Q0004433Q0013000100060E00030014000100020004433Q001400012Q0014000300034Q004C000300024Q00093Q00013Q00013Q00023Q00030C3Q00476574412Q7472696275746503043Q005469657200064Q00197Q00206Q000100122Q000200028Q00029Q008Q00017Q00083Q0003153Q0046696E6446697273744368696C644F66436C612Q7303093Q00506C61796572477569030E3Q0046696E6446697273744368696C6403093Q005363722Q656E477569030C3Q00486F6C64696E674672616D6503043Q0044726F70030A3Q005465787442752Q746F6E03053Q007063612Q6C002A4Q00207Q00206Q000100122Q000200028Q0002000200064Q0008000100010004433Q000800012Q001200016Q004C000100023Q00202F00013Q000300121E000300044Q003B00010003000200062B0001002000013Q0004433Q0020000100204A00013Q000400202F00010001000300121E000300054Q003B00010003000200062B0001002000013Q0004433Q0020000100204A00013Q000400201800010001000500202Q00010001000300122Q000300066Q00010003000200062Q0001002000013Q0004433Q0020000100204A00013Q000400201600010001000500202Q00010001000600202Q00010001000300122Q000300076Q00010003000200060F00010024000100010004433Q002400012Q001200026Q004C000200023Q001244000200083Q00063400033Q000100012Q00043Q00014Q000B000200034Q001500026Q00093Q00013Q00013Q000D3Q0003103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A6503043Q006D61746803053Q00666C2Q6F7203013Q0058027Q004003013Q0059030C3Q006D6F7573656D6F766561627303043Q007461736B03043Q0077616974029A5Q99A93F030B3Q006D6F757365317072652Q73030D3Q006D6F7573653172656C6561736500234Q003E7Q00206Q00014Q00015Q00202Q00010001000200122Q000200033Q00202Q00020002000400202Q00033Q000500202Q00040001000500202Q0004000400064Q0003000300044Q00020002000200122Q000300033Q00202Q00030003000400202Q00043Q000700202Q00050001000700202Q0005000500064Q0004000400054Q00030002000200122Q000400086Q000500026Q000600036Q00040006000100122Q000400093Q00202Q00040004000A00122Q0005000B6Q00040002000100122Q0004000C6Q00040001000100122Q000400093Q00202Q00040004000A00122Q0005000B6Q00040002000100122Q0004000D6Q0004000100016Q00017Q000C3Q0003043Q007461736B03043Q007761697403043Q006D61746803043Q006875676503093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403063Q0069706169727303083Q00506F736974696F6E03093Q004D61676E697475646503053Q00737061776E027Q0040007D3Q0012443Q00013Q0020015Q00024Q00019Q00000200016Q00013Q00064Q0008000100010004433Q000800010004435Q00012Q002A3Q00024Q00253Q0001000200062B3Q004900013Q0004433Q004900012Q002A000100034Q002500010001000200062B0001001500013Q0004433Q001500012Q002A000200044Q0004000300014Q002E00020002000200060F00020016000100010004433Q001600012Q000600026Q0014000300033Q001238000400033Q00202Q0004000400044Q000500053Q00202Q00050005000500062Q00060020000100050004433Q0020000100202F00060005000600121E000800074Q003B000600080002001244000700084Q0004000800024Q00290007000200090004433Q003700012Q002A000C00064Q0004000D000B4Q002E000C00020002000630000C003700013Q0004433Q003700012Q002A000D00074Q0004000E000B4Q002E000D0002000200062B000D003700013Q0004433Q0037000100062B0006003700013Q0004433Q0037000100204A000E000600092Q0042000E000D000E00204A000E000E000A000603000E0037000100040004433Q003700012Q00040004000E4Q00040003000B3Q00063300070024000100020004433Q0024000100062B0003004600013Q0004433Q004600012Q002A000700074Q0004000800034Q002E000700020002001244000800013Q00204A00080008000B00063400093Q000100022Q002A3Q00084Q00043Q00074Q00370008000200012Q004500075Q0004435Q00012Q002A000700094Q00350007000100010004435Q00012Q002A000100034Q002500010001000200060F0001004E000100010004433Q004E00010004435Q00012Q002A000200044Q0004000300014Q002E0002000200022Q0032000300023Q00263D000300550001000C0004433Q005500010004435Q00012Q002A0003000A4Q0004000400024Q002900030002000400060F0003005B000100010004433Q005B00010004435Q00012Q002A000500074Q0004000600034Q002E00050002000200060F00050061000100010004433Q006100010004435Q00012Q002A000600053Q00204A00060006000500064000070068000100060004433Q0068000100202F00070006000600121E000900074Q003B00070009000200060F0007006B000100010004433Q006B00010004435Q000100204A0008000700092Q004200080005000800204A00080008000A2Q002A0009000B3Q00060300090077000100080004433Q00770001001244000900013Q00204A00090009000B000634000A0001000100022Q002A3Q00084Q00043Q00054Q00370009000200012Q00457Q0004435Q00012Q00457Q0004435Q00010004435Q00012Q00093Q00013Q00028Q00044Q002A8Q002A000100014Q00373Q000200012Q00093Q00019Q003Q00044Q002A8Q002A000100014Q00373Q000200012Q00093Q00017Q000C3Q0003073Q0053656374696F6E03083Q0053652Q74696E677303043Q004C65667403063Q00546F2Q676C6503113Q006E756B656D657267655F656E61626C656403073Q00456E61626C656403093Q00536C69646572496E74030F3Q006E756B656D657267655F73702Q6564030A3Q0057616C6B2053702Q6564026Q001440025Q00C0724003093Q0057616C6B53702Q656401163Q00204100013Q000100122Q000300023Q00122Q000400036Q00010004000200202Q00020001000400122Q000400053Q00122Q000500066Q000600013Q00063400073Q000100012Q002A8Q000D00020007000100202Q00020001000700122Q000400083Q00122Q000500093Q00122Q0006000A3Q00122Q0007000B6Q000800013Q00202Q00080008000C00063400090001000100012Q002A3Q00014Q00230002000900012Q00093Q00013Q00027Q0001024Q00468Q00093Q00017Q00013Q0003093Q0057616C6B53702Q656401034Q002A00015Q001048000100014Q00093Q00017Q00", GetFEnv(), ...);
