typedef unsigned _ExtInt(1) w1;
typedef unsigned _ExtInt(2) w2;
typedef unsigned _ExtInt(4) w4;
typedef unsigned _ExtInt(8) w8;
typedef unsigned _ExtInt(32) w32;
w1 static rotl1(w1 x, w1 shf)
{
    w1 offset = 1;
    return x << shf | x >> offset - shf;
}
w1 static rotr1(w1 x, w1 shf)
{
    w1 offset = 1;
    return x >> shf | x << offset - shf;
}
w2 static rotl2(w2 x, w2 shf)
{
    w2 offset = 2;
    return x << shf | x >> offset - shf;
}
w2 static rotr2(w2 x, w2 shf)
{
    w2 offset = 2;
    return x >> shf | x << offset - shf;
}
w4 static rotl4(w4 x, w4 shf)
{
    w4 offset = 4;
    return x << shf | x >> offset - shf;
}
w4 static rotr4(w4 x, w4 shf)
{
    w4 offset = 4;
    return x >> shf | x << offset - shf;
}
w8 static rotl8(w8 x, w8 shf)
{
    w8 offset = 8;
    return x << shf | x >> offset - shf;
}
w8 static rotr8(w8 x, w8 shf)
{
    w8 offset = 8;
    return x >> shf | x << offset - shf;
}
w32 static rotl32(w32 x, w32 shf)
{
    w32 offset = 32;
    return x << shf | x >> offset - shf;
}
w32 static rotr32(w32 x, w32 shf)
{
    w32 offset = 32;
    return x >> shf | x << offset - shf;
}
w1 Actuate_D0(w8 trips4826[3][4], w1 old4827)
{
    w1 app_4179;
    w1 app_4180;
    w1 app_4181;
    w1 app_4182;
    w1 app_4183;
    w1 app_4185;
    w1 app_4186;
    w1 app_4187;
    w1 app_4188;
    w1 app_4189;
    w1 app_4191;
    w1 app_4192;
    w1 app_4193;
    w1 app_4194;
    w1 app_4195;
    w1 app_4197;
    w1 app_4198;
    w1 app_4199;
    w1 app_4200;
    w1 app_4201;
    w1 app_4203;
    w1 app_4204;
    w1 app_4205;
    w1 app_4206;
    w1 app_4207;
    w1 app_4208;
    w1 app_4209;
    w1 app_4210;
    w1 app_4211;
    w1 app_4213;
    w1 app_4214;
    w1 app_4215;
    w1 app_4216;
    w1 app_4217;
    w1 app_4219;
    w1 app_4220;
    w1 app_4221;
    w1 app_4222;
    w1 app_4223;
    w1 app_4225;
    w1 app_4226;
    w1 app_4227;
    w1 app_4228;
    w1 app_4229;
    w1 app_4231;
    w1 app_4232;
    w1 app_4233;
    w1 app_4234;
    w1 app_4235;
    w1 app_4237;
    w1 app_4238;
    w1 app_4239;
    w1 app_4240;
    w1 app_4241;
    w1 app_4242;
    w1 app_4243;
    w1 app_4244;
    w1 app_4245;
    w1 app_4246;
    w1 app_4247;
    w4 arrv_4178;
    w4 arrv_4184;
    w4 arrv_4190;
    w4 arrv_4196;
    w4 arrv_4202;
    w4 arrv_4212;
    w4 arrv_4218;
    w4 arrv_4224;
    w4 arrv_4230;
    w4 arrv_4236;
    w1 return_4100;
    return_4100 = 0;
    app_4179 = trips4826[(w2) 0][(w32) 0] != (w8) 0;
    app_4180 = trips4826[(w2) 0][(w32) 1] != (w8) 0;
    app_4181 = trips4826[(w2) 0][(w32) 2] != (w8) 0;
    app_4182 = trips4826[(w2) 0][(w32) 3] != (w8) 0;
    arrv_4178 = 0;
    if (app_4179)
    {
        arrv_4178 |= (w4) app_4179 << 0;
    }
    else
    {
        arrv_4178 &= ~((w4) 1 << 0);
    }
    if (app_4180)
    {
        arrv_4178 |= (w4) app_4180 << 1;
    }
    else
    {
        arrv_4178 &= ~((w4) 1 << 1);
    }
    if (app_4181)
    {
        arrv_4178 |= (w4) app_4181 << 2;
    }
    else
    {
        arrv_4178 &= ~((w4) 1 << 2);
    }
    if (app_4182)
    {
        arrv_4178 |= (w4) app_4182 << 3;
    }
    else
    {
        arrv_4178 &= ~((w4) 1 << 3);
    }
    app_4183 = arrv_4178 != (w4) 0;
    app_4185 = trips4826[(w2) 0][(w32) 0] != (w8) 0;
    app_4186 = trips4826[(w2) 0][(w32) 1] != (w8) 0;
    app_4187 = trips4826[(w2) 0][(w32) 2] != (w8) 0;
    app_4188 = trips4826[(w2) 0][(w32) 3] != (w8) 0;
    arrv_4184 = 0;
    if (app_4185)
    {
        arrv_4184 |= (w4) app_4185 << 0;
    }
    else
    {
        arrv_4184 &= ~((w4) 1 << 0);
    }
    if (app_4186)
    {
        arrv_4184 |= (w4) app_4186 << 1;
    }
    else
    {
        arrv_4184 &= ~((w4) 1 << 1);
    }
    if (app_4187)
    {
        arrv_4184 |= (w4) app_4187 << 2;
    }
    else
    {
        arrv_4184 &= ~((w4) 1 << 2);
    }
    if (app_4188)
    {
        arrv_4184 |= (w4) app_4188 << 3;
    }
    else
    {
        arrv_4184 &= ~((w4) 1 << 3);
    }
    app_4189 = arrv_4184 != (w4) 1;
    app_4191 = trips4826[(w2) 0][(w32) 0] != (w8) 0;
    app_4192 = trips4826[(w2) 0][(w32) 1] != (w8) 0;
    app_4193 = trips4826[(w2) 0][(w32) 2] != (w8) 0;
    app_4194 = trips4826[(w2) 0][(w32) 3] != (w8) 0;
    arrv_4190 = 0;
    if (app_4191)
    {
        arrv_4190 |= (w4) app_4191 << 0;
    }
    else
    {
        arrv_4190 &= ~((w4) 1 << 0);
    }
    if (app_4192)
    {
        arrv_4190 |= (w4) app_4192 << 1;
    }
    else
    {
        arrv_4190 &= ~((w4) 1 << 1);
    }
    if (app_4193)
    {
        arrv_4190 |= (w4) app_4193 << 2;
    }
    else
    {
        arrv_4190 &= ~((w4) 1 << 2);
    }
    if (app_4194)
    {
        arrv_4190 |= (w4) app_4194 << 3;
    }
    else
    {
        arrv_4190 &= ~((w4) 1 << 3);
    }
    app_4195 = arrv_4190 != (w4) 2;
    app_4197 = trips4826[(w2) 0][(w32) 0] != (w8) 0;
    app_4198 = trips4826[(w2) 0][(w32) 1] != (w8) 0;
    app_4199 = trips4826[(w2) 0][(w32) 2] != (w8) 0;
    app_4200 = trips4826[(w2) 0][(w32) 3] != (w8) 0;
    arrv_4196 = 0;
    if (app_4197)
    {
        arrv_4196 |= (w4) app_4197 << 0;
    }
    else
    {
        arrv_4196 &= ~((w4) 1 << 0);
    }
    if (app_4198)
    {
        arrv_4196 |= (w4) app_4198 << 1;
    }
    else
    {
        arrv_4196 &= ~((w4) 1 << 1);
    }
    if (app_4199)
    {
        arrv_4196 |= (w4) app_4199 << 2;
    }
    else
    {
        arrv_4196 &= ~((w4) 1 << 2);
    }
    if (app_4200)
    {
        arrv_4196 |= (w4) app_4200 << 3;
    }
    else
    {
        arrv_4196 &= ~((w4) 1 << 3);
    }
    app_4201 = arrv_4196 != (w4) 4;
    app_4203 = trips4826[(w2) 0][(w32) 0] != (w8) 0;
    app_4204 = trips4826[(w2) 0][(w32) 1] != (w8) 0;
    app_4205 = trips4826[(w2) 0][(w32) 2] != (w8) 0;
    app_4206 = trips4826[(w2) 0][(w32) 3] != (w8) 0;
    arrv_4202 = 0;
    if (app_4203)
    {
        arrv_4202 |= (w4) app_4203 << 0;
    }
    else
    {
        arrv_4202 &= ~((w4) 1 << 0);
    }
    if (app_4204)
    {
        arrv_4202 |= (w4) app_4204 << 1;
    }
    else
    {
        arrv_4202 &= ~((w4) 1 << 1);
    }
    if (app_4205)
    {
        arrv_4202 |= (w4) app_4205 << 2;
    }
    else
    {
        arrv_4202 &= ~((w4) 1 << 2);
    }
    if (app_4206)
    {
        arrv_4202 |= (w4) app_4206 << 3;
    }
    else
    {
        arrv_4202 &= ~((w4) 1 << 3);
    }
    app_4207 = arrv_4202 != (w4) 8;
    app_4208 = app_4201 & app_4207;
    app_4209 = app_4195 & app_4208;
    app_4210 = app_4189 & app_4209;
    app_4211 = app_4183 & app_4210;
    app_4213 = trips4826[(w2) 1][(w32) 0] != (w8) 0;
    app_4214 = trips4826[(w2) 1][(w32) 1] != (w8) 0;
    app_4215 = trips4826[(w2) 1][(w32) 2] != (w8) 0;
    app_4216 = trips4826[(w2) 1][(w32) 3] != (w8) 0;
    arrv_4212 = 0;
    if (app_4213)
    {
        arrv_4212 |= (w4) app_4213 << 0;
    }
    else
    {
        arrv_4212 &= ~((w4) 1 << 0);
    }
    if (app_4214)
    {
        arrv_4212 |= (w4) app_4214 << 1;
    }
    else
    {
        arrv_4212 &= ~((w4) 1 << 1);
    }
    if (app_4215)
    {
        arrv_4212 |= (w4) app_4215 << 2;
    }
    else
    {
        arrv_4212 &= ~((w4) 1 << 2);
    }
    if (app_4216)
    {
        arrv_4212 |= (w4) app_4216 << 3;
    }
    else
    {
        arrv_4212 &= ~((w4) 1 << 3);
    }
    app_4217 = arrv_4212 != (w4) 0;
    app_4219 = trips4826[(w2) 1][(w32) 0] != (w8) 0;
    app_4220 = trips4826[(w2) 1][(w32) 1] != (w8) 0;
    app_4221 = trips4826[(w2) 1][(w32) 2] != (w8) 0;
    app_4222 = trips4826[(w2) 1][(w32) 3] != (w8) 0;
    arrv_4218 = 0;
    if (app_4219)
    {
        arrv_4218 |= (w4) app_4219 << 0;
    }
    else
    {
        arrv_4218 &= ~((w4) 1 << 0);
    }
    if (app_4220)
    {
        arrv_4218 |= (w4) app_4220 << 1;
    }
    else
    {
        arrv_4218 &= ~((w4) 1 << 1);
    }
    if (app_4221)
    {
        arrv_4218 |= (w4) app_4221 << 2;
    }
    else
    {
        arrv_4218 &= ~((w4) 1 << 2);
    }
    if (app_4222)
    {
        arrv_4218 |= (w4) app_4222 << 3;
    }
    else
    {
        arrv_4218 &= ~((w4) 1 << 3);
    }
    app_4223 = arrv_4218 != (w4) 1;
    app_4225 = trips4826[(w2) 1][(w32) 0] != (w8) 0;
    app_4226 = trips4826[(w2) 1][(w32) 1] != (w8) 0;
    app_4227 = trips4826[(w2) 1][(w32) 2] != (w8) 0;
    app_4228 = trips4826[(w2) 1][(w32) 3] != (w8) 0;
    arrv_4224 = 0;
    if (app_4225)
    {
        arrv_4224 |= (w4) app_4225 << 0;
    }
    else
    {
        arrv_4224 &= ~((w4) 1 << 0);
    }
    if (app_4226)
    {
        arrv_4224 |= (w4) app_4226 << 1;
    }
    else
    {
        arrv_4224 &= ~((w4) 1 << 1);
    }
    if (app_4227)
    {
        arrv_4224 |= (w4) app_4227 << 2;
    }
    else
    {
        arrv_4224 &= ~((w4) 1 << 2);
    }
    if (app_4228)
    {
        arrv_4224 |= (w4) app_4228 << 3;
    }
    else
    {
        arrv_4224 &= ~((w4) 1 << 3);
    }
    app_4229 = arrv_4224 != (w4) 2;
    app_4231 = trips4826[(w2) 1][(w32) 0] != (w8) 0;
    app_4232 = trips4826[(w2) 1][(w32) 1] != (w8) 0;
    app_4233 = trips4826[(w2) 1][(w32) 2] != (w8) 0;
    app_4234 = trips4826[(w2) 1][(w32) 3] != (w8) 0;
    arrv_4230 = 0;
    if (app_4231)
    {
        arrv_4230 |= (w4) app_4231 << 0;
    }
    else
    {
        arrv_4230 &= ~((w4) 1 << 0);
    }
    if (app_4232)
    {
        arrv_4230 |= (w4) app_4232 << 1;
    }
    else
    {
        arrv_4230 &= ~((w4) 1 << 1);
    }
    if (app_4233)
    {
        arrv_4230 |= (w4) app_4233 << 2;
    }
    else
    {
        arrv_4230 &= ~((w4) 1 << 2);
    }
    if (app_4234)
    {
        arrv_4230 |= (w4) app_4234 << 3;
    }
    else
    {
        arrv_4230 &= ~((w4) 1 << 3);
    }
    app_4235 = arrv_4230 != (w4) 4;
    app_4237 = trips4826[(w2) 1][(w32) 0] != (w8) 0;
    app_4238 = trips4826[(w2) 1][(w32) 1] != (w8) 0;
    app_4239 = trips4826[(w2) 1][(w32) 2] != (w8) 0;
    app_4240 = trips4826[(w2) 1][(w32) 3] != (w8) 0;
    arrv_4236 = 0;
    if (app_4237)
    {
        arrv_4236 |= (w4) app_4237 << 0;
    }
    else
    {
        arrv_4236 &= ~((w4) 1 << 0);
    }
    if (app_4238)
    {
        arrv_4236 |= (w4) app_4238 << 1;
    }
    else
    {
        arrv_4236 &= ~((w4) 1 << 1);
    }
    if (app_4239)
    {
        arrv_4236 |= (w4) app_4239 << 2;
    }
    else
    {
        arrv_4236 &= ~((w4) 1 << 2);
    }
    if (app_4240)
    {
        arrv_4236 |= (w4) app_4240 << 3;
    }
    else
    {
        arrv_4236 &= ~((w4) 1 << 3);
    }
    app_4241 = arrv_4236 != (w4) 8;
    app_4242 = app_4235 & app_4241;
    app_4243 = app_4229 & app_4242;
    app_4244 = app_4223 & app_4243;
    app_4245 = app_4217 & app_4244;
    app_4246 = app_4211 | app_4245;
    app_4247 = app_4246 | old4827;
    return_4100 = app_4247;
    return return_4100;
}
w1 Actuate_D1(w8 trips4822[3][4], w1 old4823)
{
    w1 app_4253;
    w1 app_4254;
    w1 app_4255;
    w1 app_4256;
    w1 app_4257;
    w1 app_4259;
    w1 app_4260;
    w1 app_4261;
    w1 app_4262;
    w1 app_4263;
    w1 app_4265;
    w1 app_4266;
    w1 app_4267;
    w1 app_4268;
    w1 app_4269;
    w1 app_4271;
    w1 app_4272;
    w1 app_4273;
    w1 app_4274;
    w1 app_4275;
    w1 app_4277;
    w1 app_4278;
    w1 app_4279;
    w1 app_4280;
    w1 app_4281;
    w1 app_4282;
    w1 app_4283;
    w1 app_4284;
    w1 app_4285;
    w1 app_4286;
    w4 arrv_4252;
    w4 arrv_4258;
    w4 arrv_4264;
    w4 arrv_4270;
    w4 arrv_4276;
    w1 return_4249;
    return_4249 = 0;
    app_4253 = trips4822[(w2) 2][(w32) 0] != (w8) 0;
    app_4254 = trips4822[(w2) 2][(w32) 1] != (w8) 0;
    app_4255 = trips4822[(w2) 2][(w32) 2] != (w8) 0;
    app_4256 = trips4822[(w2) 2][(w32) 3] != (w8) 0;
    arrv_4252 = 0;
    if (app_4253)
    {
        arrv_4252 |= (w4) app_4253 << 0;
    }
    else
    {
        arrv_4252 &= ~((w4) 1 << 0);
    }
    if (app_4254)
    {
        arrv_4252 |= (w4) app_4254 << 1;
    }
    else
    {
        arrv_4252 &= ~((w4) 1 << 1);
    }
    if (app_4255)
    {
        arrv_4252 |= (w4) app_4255 << 2;
    }
    else
    {
        arrv_4252 &= ~((w4) 1 << 2);
    }
    if (app_4256)
    {
        arrv_4252 |= (w4) app_4256 << 3;
    }
    else
    {
        arrv_4252 &= ~((w4) 1 << 3);
    }
    app_4257 = arrv_4252 != (w4) 0;
    app_4259 = trips4822[(w2) 2][(w32) 0] != (w8) 0;
    app_4260 = trips4822[(w2) 2][(w32) 1] != (w8) 0;
    app_4261 = trips4822[(w2) 2][(w32) 2] != (w8) 0;
    app_4262 = trips4822[(w2) 2][(w32) 3] != (w8) 0;
    arrv_4258 = 0;
    if (app_4259)
    {
        arrv_4258 |= (w4) app_4259 << 0;
    }
    else
    {
        arrv_4258 &= ~((w4) 1 << 0);
    }
    if (app_4260)
    {
        arrv_4258 |= (w4) app_4260 << 1;
    }
    else
    {
        arrv_4258 &= ~((w4) 1 << 1);
    }
    if (app_4261)
    {
        arrv_4258 |= (w4) app_4261 << 2;
    }
    else
    {
        arrv_4258 &= ~((w4) 1 << 2);
    }
    if (app_4262)
    {
        arrv_4258 |= (w4) app_4262 << 3;
    }
    else
    {
        arrv_4258 &= ~((w4) 1 << 3);
    }
    app_4263 = arrv_4258 != (w4) 1;
    app_4265 = trips4822[(w2) 2][(w32) 0] != (w8) 0;
    app_4266 = trips4822[(w2) 2][(w32) 1] != (w8) 0;
    app_4267 = trips4822[(w2) 2][(w32) 2] != (w8) 0;
    app_4268 = trips4822[(w2) 2][(w32) 3] != (w8) 0;
    arrv_4264 = 0;
    if (app_4265)
    {
        arrv_4264 |= (w4) app_4265 << 0;
    }
    else
    {
        arrv_4264 &= ~((w4) 1 << 0);
    }
    if (app_4266)
    {
        arrv_4264 |= (w4) app_4266 << 1;
    }
    else
    {
        arrv_4264 &= ~((w4) 1 << 1);
    }
    if (app_4267)
    {
        arrv_4264 |= (w4) app_4267 << 2;
    }
    else
    {
        arrv_4264 &= ~((w4) 1 << 2);
    }
    if (app_4268)
    {
        arrv_4264 |= (w4) app_4268 << 3;
    }
    else
    {
        arrv_4264 &= ~((w4) 1 << 3);
    }
    app_4269 = arrv_4264 != (w4) 2;
    app_4271 = trips4822[(w2) 2][(w32) 0] != (w8) 0;
    app_4272 = trips4822[(w2) 2][(w32) 1] != (w8) 0;
    app_4273 = trips4822[(w2) 2][(w32) 2] != (w8) 0;
    app_4274 = trips4822[(w2) 2][(w32) 3] != (w8) 0;
    arrv_4270 = 0;
    if (app_4271)
    {
        arrv_4270 |= (w4) app_4271 << 0;
    }
    else
    {
        arrv_4270 &= ~((w4) 1 << 0);
    }
    if (app_4272)
    {
        arrv_4270 |= (w4) app_4272 << 1;
    }
    else
    {
        arrv_4270 &= ~((w4) 1 << 1);
    }
    if (app_4273)
    {
        arrv_4270 |= (w4) app_4273 << 2;
    }
    else
    {
        arrv_4270 &= ~((w4) 1 << 2);
    }
    if (app_4274)
    {
        arrv_4270 |= (w4) app_4274 << 3;
    }
    else
    {
        arrv_4270 &= ~((w4) 1 << 3);
    }
    app_4275 = arrv_4270 != (w4) 4;
    app_4277 = trips4822[(w2) 2][(w32) 0] != (w8) 0;
    app_4278 = trips4822[(w2) 2][(w32) 1] != (w8) 0;
    app_4279 = trips4822[(w2) 2][(w32) 2] != (w8) 0;
    app_4280 = trips4822[(w2) 2][(w32) 3] != (w8) 0;
    arrv_4276 = 0;
    if (app_4277)
    {
        arrv_4276 |= (w4) app_4277 << 0;
    }
    else
    {
        arrv_4276 &= ~((w4) 1 << 0);
    }
    if (app_4278)
    {
        arrv_4276 |= (w4) app_4278 << 1;
    }
    else
    {
        arrv_4276 &= ~((w4) 1 << 1);
    }
    if (app_4279)
    {
        arrv_4276 |= (w4) app_4279 << 2;
    }
    else
    {
        arrv_4276 &= ~((w4) 1 << 2);
    }
    if (app_4280)
    {
        arrv_4276 |= (w4) app_4280 << 3;
    }
    else
    {
        arrv_4276 &= ~((w4) 1 << 3);
    }
    app_4281 = arrv_4276 != (w4) 8;
    app_4282 = app_4275 & app_4281;
    app_4283 = app_4269 & app_4282;
    app_4284 = app_4263 & app_4283;
    app_4285 = app_4257 & app_4284;
    app_4286 = app_4285 | old4823;
    return_4249 = app_4286;
    return return_4249;
}
