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
w1 Coincidence_2_4(w4 x4846)
{
    w1 app_4097;
    w1 app_4098;
    w1 app_4099;
    w1 app_4100;
    w1 app_4101;
    w1 app_4102;
    w1 app_4103;
    w1 app_4104;
    w1 app_4105;
    w1 return_4096;
    return_4096 = 0;
    app_4097 = x4846 != (w4) 0;
    app_4098 = x4846 != (w4) 1;
    app_4099 = x4846 != (w4) 2;
    app_4100 = x4846 != (w4) 4;
    app_4101 = x4846 != (w4) 8;
    app_4102 = app_4100 & app_4101;
    app_4103 = app_4099 & app_4102;
    app_4104 = app_4098 & app_4103;
    app_4105 = app_4097 & app_4104;
    return_4096 = app_4105;
    return return_4096;
}
w2 Voting_Step(w8 inp4829[4][3], w2 old_votes4830)
{
    w1 app_4140;
    w1 app_4141;
    w1 app_4142;
    w1 app_4143;
    w1 app_4144;
    w1 app_4146;
    w1 app_4147;
    w1 app_4148;
    w1 app_4149;
    w1 app_4150;
    w1 app_4151;
    w1 app_4152;
    w1 app_4154;
    w1 app_4155;
    w1 app_4156;
    w1 app_4157;
    w1 app_4158;
    w1 app_4159;
    w4 arrv_4139;
    w4 arrv_4145;
    w4 arrv_4153;
    w2 return_4107;
    return_4107 = 0;
    app_4140 = inp4829[(w32) 0][(w2) 0] == (w8) 1;
    app_4141 = inp4829[(w32) 1][(w2) 0] == (w8) 1;
    app_4142 = inp4829[(w32) 2][(w2) 0] == (w8) 1;
    app_4143 = inp4829[(w32) 3][(w2) 0] == (w8) 1;
    arrv_4139 = 0;
    if (app_4140)
    {
        arrv_4139 |= (w4) app_4140 << 0;
    }
    else
    {
        arrv_4139 &= ~((w4) 1 << 0);
    }
    if (app_4141)
    {
        arrv_4139 |= (w4) app_4141 << 1;
    }
    else
    {
        arrv_4139 &= ~((w4) 1 << 1);
    }
    if (app_4142)
    {
        arrv_4139 |= (w4) app_4142 << 2;
    }
    else
    {
        arrv_4139 &= ~((w4) 1 << 2);
    }
    if (app_4143)
    {
        arrv_4139 |= (w4) app_4143 << 3;
    }
    else
    {
        arrv_4139 &= ~((w4) 1 << 3);
    }
    app_4144 = Coincidence_2_4(arrv_4139);
    app_4146 = inp4829[(w32) 0][(w2) 1] == (w8) 1;
    app_4147 = inp4829[(w32) 1][(w2) 1] == (w8) 1;
    app_4148 = inp4829[(w32) 2][(w2) 1] == (w8) 1;
    app_4149 = inp4829[(w32) 3][(w2) 1] == (w8) 1;
    arrv_4145 = 0;
    if (app_4146)
    {
        arrv_4145 |= (w4) app_4146 << 0;
    }
    else
    {
        arrv_4145 &= ~((w4) 1 << 0);
    }
    if (app_4147)
    {
        arrv_4145 |= (w4) app_4147 << 1;
    }
    else
    {
        arrv_4145 &= ~((w4) 1 << 1);
    }
    if (app_4148)
    {
        arrv_4145 |= (w4) app_4148 << 2;
    }
    else
    {
        arrv_4145 &= ~((w4) 1 << 2);
    }
    if (app_4149)
    {
        arrv_4145 |= (w4) app_4149 << 3;
    }
    else
    {
        arrv_4145 &= ~((w4) 1 << 3);
    }
    app_4150 = Coincidence_2_4(arrv_4145);
    app_4151 = app_4150 | old_votes4830 >> (w1) 0 & 1;
    app_4152 = app_4144 | app_4151;
    app_4154 = inp4829[(w32) 0][(w2) 2] == (w8) 1;
    app_4155 = inp4829[(w32) 1][(w2) 2] == (w8) 1;
    app_4156 = inp4829[(w32) 2][(w2) 2] == (w8) 1;
    app_4157 = inp4829[(w32) 3][(w2) 2] == (w8) 1;
    arrv_4153 = 0;
    if (app_4154)
    {
        arrv_4153 |= (w4) app_4154 << 0;
    }
    else
    {
        arrv_4153 &= ~((w4) 1 << 0);
    }
    if (app_4155)
    {
        arrv_4153 |= (w4) app_4155 << 1;
    }
    else
    {
        arrv_4153 &= ~((w4) 1 << 1);
    }
    if (app_4156)
    {
        arrv_4153 |= (w4) app_4156 << 2;
    }
    else
    {
        arrv_4153 &= ~((w4) 1 << 2);
    }
    if (app_4157)
    {
        arrv_4153 |= (w4) app_4157 << 3;
    }
    else
    {
        arrv_4153 &= ~((w4) 1 << 3);
    }
    app_4158 = Coincidence_2_4(arrv_4153);
    app_4159 = app_4158 | old_votes4830 >> (w1) 1 & 1;
    if (app_4152)
    {
        return_4107 |= (w2) 1 << (w32) 0;
    }
    else
    {
        return_4107 &= ~((w2) 1 << (w32) 0);
    }
    if (app_4159)
    {
        return_4107 |= (w2) 1 << (w32) 1;
    }
    else
    {
        return_4107 &= ~((w2) 1 << (w32) 1);
    }
    return return_4107;
}
