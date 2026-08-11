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
				if (Enum <= 39) then
					if (Enum <= 19) then
						if (Enum <= 9) then
							if (Enum <= 4) then
								if (Enum <= 1) then
									if (Enum > 0) then
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
											if (Mvm[1] == 13) then
												Indexes[Idx - 1] = {Stk,Mvm[3]};
											else
												Indexes[Idx - 1] = {Upvalues,Mvm[3]};
											end
											Lupvals[#Lupvals + 1] = Indexes;
										end
										Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
									else
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
											if (Mvm[1] == 13) then
												Indexes[Idx - 1] = {Stk,Mvm[3]};
											else
												Indexes[Idx - 1] = {Upvalues,Mvm[3]};
											end
											Lupvals[#Lupvals + 1] = Indexes;
										end
										Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
									end
								elseif (Enum <= 2) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum > 3) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 6) then
								if (Enum > 5) then
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
								end
							elseif (Enum <= 7) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							elseif (Enum > 8) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 14) then
							if (Enum <= 11) then
								if (Enum == 10) then
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 12) then
								local A = Inst[2];
								local Step = Stk[A + 2];
								local Index = Stk[A] + Step;
								Stk[A] = Index;
								if (Step > 0) then
									if (Index <= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								elseif (Index >= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Enum > 13) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 16) then
							if (Enum == 15) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 17) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						elseif (Enum > 18) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 29) then
						if (Enum <= 24) then
							if (Enum <= 21) then
								if (Enum == 20) then
									Stk[Inst[2]] = {};
								else
									do
										return;
									end
								end
							elseif (Enum <= 22) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 23) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 26) then
							if (Enum > 25) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = -Stk[Inst[3]];
							end
						elseif (Enum <= 27) then
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Top do
								Insert(T, Stk[Idx]);
							end
						elseif (Enum > 28) then
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
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 34) then
						if (Enum <= 31) then
							if (Enum > 30) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 32) then
							Stk[Inst[2]]();
						elseif (Enum > 33) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]]();
						end
					elseif (Enum <= 36) then
						if (Enum > 35) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 37) then
						if (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 38) then
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
					else
						do
							return;
						end
					end
				elseif (Enum <= 59) then
					if (Enum <= 49) then
						if (Enum <= 44) then
							if (Enum <= 41) then
								if (Enum == 40) then
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local Step = Stk[A + 2];
									local Index = Stk[A] + Step;
									Stk[A] = Index;
									if (Step > 0) then
										if (Index <= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Index >= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								end
							elseif (Enum <= 42) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							elseif (Enum > 43) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 46) then
							if (Enum == 45) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 47) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum > 48) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						end
					elseif (Enum <= 54) then
						if (Enum <= 51) then
							if (Enum == 50) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							end
						elseif (Enum <= 52) then
							Stk[Inst[2]] = Stk[Inst[3]];
						elseif (Enum == 53) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 56) then
						if (Enum == 55) then
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
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
					elseif (Enum <= 57) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					elseif (Enum == 58) then
						Stk[Inst[2]] = {};
					else
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
					end
				elseif (Enum <= 69) then
					if (Enum <= 64) then
						if (Enum <= 61) then
							if (Enum == 60) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 62) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						elseif (Enum == 63) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						else
							local A = Inst[2];
							local Index = Stk[A];
							local Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum <= 66) then
						if (Enum > 65) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 67) then
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					elseif (Enum > 68) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 74) then
					if (Enum <= 71) then
						if (Enum == 70) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]] = -Stk[Inst[3]];
						end
					elseif (Enum <= 72) then
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
					elseif (Enum > 73) then
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif not Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 76) then
					if (Enum == 75) then
						local A = Inst[2];
						local Index = Stk[A];
						local Step = Stk[A + 2];
						if (Step > 0) then
							if (Index > Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						elseif (Index < Stk[A + 1]) then
							VIP = Inst[3];
						else
							Stk[A + 3] = Index;
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
					end
				elseif (Enum <= 77) then
					Stk[Inst[2]] = Env[Inst[3]];
				elseif (Enum == 78) then
					local A = Inst[2];
					local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
					Top = (Limit + A) - 1;
					local Edx = 0;
					for Idx = A, Top do
						Edx = Edx + 1;
						Stk[Idx] = Results[Edx];
					end
				else
					Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!0C3Q0003043Q0067616D6503093Q00576F726B7370616365030E3Q00426F756E747956656869636C657303083Q0056656869636C657303063Q00697061697273030B3Q004765744368696C6472656E03043Q007461736B03053Q00737061776E03063Q006E6F74696679030B3Q0056656869636C652045535003063Q004C6F61646564026Q00084000263Q0012223Q00013Q0020395Q00020020395Q00030020395Q00042Q001400015Q00060100023Q000100012Q000D3Q00013Q00060100030001000100012Q000D3Q00013Q001222000400053Q00204200053Q00062Q0038000500064Q000400043Q000600041F3Q001100012Q0034000900024Q0034000A00084Q000800090002000100061D0004000E0001000200041F3Q000E0001001222000400073Q00203900040004000800060100050002000100042Q000D8Q000D3Q00024Q000D3Q00014Q000D3Q00034Q0008000400020001001222000400073Q00203900040004000800060100050003000100012Q000D3Q00014Q0008000400020001001222000400093Q002Q120005000A3Q002Q120006000B3Q002Q120007000C4Q00020004000700012Q00153Q00013Q00043Q00203Q00030E3Q0046696E6446697273744368696C6403043Q00426F6479028Q0003063Q00697061697273030E3Q0047657444657363656E64616E747303043Q004E616D65030D3Q00436F2Q6C6973696F6E5061727403043Q0053697A6503013Q005803013Q005903013Q005A026Q00F03F026Q00104003073Q0044726177696E672Q033Q006E657703043Q004C696E6503053Q00436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742025Q00E06F4003093Q00546869636B6E652Q73027Q004003073Q0056697369626C65010003043Q005465787403063Q0043656E7465722Q0103073Q004F75746C696E65026Q002A4003043Q007061727403053Q006C696E657303043Q006E616D6501554Q001E00016Q0035000100013Q00064A0001000500013Q00041F3Q000500012Q00153Q00013Q00204200013Q0001002Q12000300024Q002F0001000300020006440001000B0001000100041F3Q000B00012Q00153Q00014Q0032000200023Q002Q12000300033Q001222000400043Q0020420005000100052Q0038000500064Q000400043Q000600041F3Q00210001002039000900080006002628000900210001000700041F3Q0021000100203900090008000800064A0009002100013Q00041F3Q00210001002039000A00090009002039000B0009000A2Q0027000A000A000B002039000B0009000B2Q0027000A000A000B000641000300210001000A00041F3Q002100012Q00340003000A4Q0034000200083Q00061D000400120001000200041F3Q00120001000644000200260001000100041F3Q002600012Q00153Q00014Q001400045Q002Q120005000C3Q002Q120006000D3Q002Q120007000C3Q0004400005003D00010012220009000E3Q00203900090009000F002Q12000A00104Q00070009000200022Q00170004000800092Q0035000900040008001222000A00123Q002039000A000A0013002Q12000B00143Q002Q12000C00033Q002Q12000D00034Q002F000A000D000200101300090011000A2Q003500090004000800302E0009001500162Q003500090004000800302E0009001700180004290005002B00010012220005000E3Q00203900050005000F002Q12000600194Q000700050002000200203900063Q0006001013000500190006001222000600123Q002039000600060013002Q12000700143Q002Q12000800143Q002Q12000900144Q002F00060009000200101300050011000600302E0005001A001B00302E0005001C001B00302E00050008001D00302E0005001700182Q001E00066Q001400073Q00030010130007001E00020010130007001F00040010130007002000052Q001700063Q00072Q00153Q00017Q00053Q0003063Q0069706169727303053Q006C696E657303063Q0052656D6F766503043Q006E616D650001134Q001E00016Q0035000100013Q000644000100050001000100041F3Q000500012Q00153Q00013Q001222000200013Q0020390003000100022Q001A00020002000400041F3Q000B00010020420007000600032Q000800070002000100061D000200090001000200041F3Q000900010020390002000100040020420002000200032Q00080002000200012Q001E00025Q00203B00023Q00052Q00153Q00017Q00073Q0003063Q00697061697273030B3Q004765744368696C6472656E2Q0103053Q00706169727303043Q007461736B03043Q0077616974026Q00F03F001F4Q00147Q001222000100014Q001E00025Q0020420002000200022Q0038000200034Q000400013Q000300041F3Q000B000100203B3Q000500032Q001E000600014Q0034000700054Q000800060002000100061D000100070001000200041F3Q00070001001222000100044Q001E000200024Q001A00010002000300041F3Q001700012Q003500053Q0004000644000500170001000100041F3Q001700012Q001E000500034Q0034000600044Q000800050002000100061D000100110001000100041F3Q00110001001222000100053Q002039000100010006002Q12000200074Q000800010002000100041F5Q00012Q00153Q00017Q00213Q0003053Q00706169727303043Q007061727403063Q00506172656E7403083Q00506F736974696F6E03043Q0053697A6503013Q0058027Q004003013Q005903013Q005A03073Q00566563746F72332Q033Q006E657703043Q006D61746803043Q006875676503063Q00697061697273030D3Q00576F726C64546F5363722Q656E2Q033Q006D696E2Q033Q006D617803053Q006C696E6573026Q00F03F03043Q0046726F6D03073Q00566563746F723203023Q00546F026Q000840026Q00104003073Q0056697369626C652Q0103043Q006E616D6503043Q005465787403043Q004E616D65026Q002840010003043Q007461736B03043Q007761697400EC3Q0012223Q00014Q001E00016Q001A3Q0002000200041F3Q00E5000100203900050004000200064A000500E500013Q00041F3Q00E5000100203900060005000300064A000600E500013Q00041F3Q00E50001002039000600050004002039000700050005002039000800070006002033000800080007002039000900070008002033000900090007002039000A00070009002033000A000A00072Q0014000B00073Q001222000C000A3Q002039000C000C000B002039000D000600062Q0009000D000D0008002039000E000600082Q0009000E000E0009002039000F000600092Q0009000F000F000A2Q002F000C000F0002001222000D000A3Q002039000D000D000B002039000E000600062Q004C000E000E0008002039000F000600082Q0009000F000F00090020390010000600092Q000900100010000A2Q002F000D00100002001222000E000A3Q002039000E000E000B002039000F000600062Q0009000F000F00080020390010000600082Q004C0010001000090020390011000600092Q000900110011000A2Q002F000E00110002001222000F000A3Q002039000F000F000B0020390010000600062Q004C0010001000080020390011000600082Q004C0011001100090020390012000600092Q000900120012000A2Q002F000F001200020012220010000A3Q00203900100010000B0020390011000600062Q00090011001100080020390012000600082Q00090012001200090020390013000600092Q004C00130013000A2Q002F0010001300020012220011000A3Q00203900110011000B0020390012000600062Q004C0012001200080020390013000600082Q00090013001300090020390014000600092Q004C00140014000A2Q002F0011001400020012220012000A3Q00203900120012000B0020390013000600062Q00090013001300080020390014000600082Q004C0014001400090020390015000600092Q004C00150015000A2Q002F0012001500020012220013000A3Q00203900130013000B0020390014000600062Q004C0014001400080020390015000600082Q004C0015001500090020390016000600092Q004C00160016000A2Q0010001300164Q001B000B3Q0001001222000C000C3Q002039000C000C000D001222000D000C3Q002039000D000D000D001222000E000C3Q002039000E000E000D2Q0047000E000E3Q001222000F000C3Q002039000F000F000D2Q0047000F000F4Q000500105Q0012220011000E4Q00340012000B4Q001A00110002001300041F3Q008900010012220016000F4Q0034001700154Q001A00160002001700064A0017008900013Q00041F3Q008900012Q0005001000013Q0012220018000C3Q0020390018001800102Q00340019000C3Q002039001A001600062Q002F0018001A00022Q0034000C00183Q0012220018000C3Q0020390018001800102Q00340019000D3Q002039001A001600082Q002F0018001A00022Q0034000D00183Q0012220018000C3Q0020390018001800112Q00340019000E3Q002039001A001600062Q002F0018001A00022Q0034000E00183Q0012220018000C3Q0020390018001800112Q00340019000F3Q002039001A001600082Q002F0018001A00022Q0034000F00183Q00061D0011006B0001000200041F3Q006B000100064A001000DC00013Q00041F3Q00DC0001002039001100040012002039001200110013001222001300153Q00203900130013000B2Q00340014000C4Q00340015000D4Q002F001300150002001013001200140013002039001200110013001222001300153Q00203900130013000B2Q00340014000E4Q00340015000D4Q002F001300150002001013001200160013002039001200110007001222001300153Q00203900130013000B2Q00340014000E4Q00340015000D4Q002F001300150002001013001200140013002039001200110007001222001300153Q00203900130013000B2Q00340014000E4Q00340015000F4Q002F001300150002001013001200160013002039001200110017001222001300153Q00203900130013000B2Q00340014000E4Q00340015000F4Q002F001300150002001013001200140013002039001200110017001222001300153Q00203900130013000B2Q00340014000C4Q00340015000F4Q002F001300150002001013001200160013002039001200110018001222001300153Q00203900130013000B2Q00340014000C4Q00340015000F4Q002F001300150002001013001200140013002039001200110018001222001300153Q00203900130013000B2Q00340014000C4Q00340015000D4Q002F0013001500020010130012001600130012220012000E4Q0034001300114Q001A00120002001400041F3Q00CB000100302E00160019001A00061D001200CA0001000200041F3Q00CA00012Q004C0012000C000E00203300120012000700203900130004001B00203900140003001D0010130013001C001400203900130004001B001222001400153Q00203900140014000B2Q0034001500123Q00202D0016000F001E2Q002F00140016000200101300130004001400203900130004001B00302E00130019001A00041F3Q00E500010012220011000E3Q0020390012000400122Q001A00110002001300041F3Q00E1000100302E00150019001F00061D001100E00001000200041F3Q00E0000100203900110004001B00302E00110019001F00061D3Q00040001000200041F3Q000400010012223Q00203Q0020395Q00212Q00213Q0001000100041F5Q00012Q00153Q00017Q00", GetFEnv(), ...);
