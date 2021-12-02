typedef unsigned _ExtInt(1) w1;
typedef unsigned _ExtInt(2) w2;
typedef unsigned _ExtInt(3) w3;
typedef unsigned _ExtInt(32) w32;
w1 rotl1(w1 x, w1 shf)
{
    w1 offset = 1;
    return x << shf | x >> offset - shf;
}
w1 rotr1(w1 x, w1 shf)
{
    w1 offset = 1;
    return x >> shf | x << offset - shf;
}
w2 rotl2(w2 x, w2 shf)
{
    w2 offset = 2;
    return x << shf | x >> offset - shf;
}
w2 rotr2(w2 x, w2 shf)
{
    w2 offset = 2;
    return x >> shf | x << offset - shf;
}
w3 rotl3(w3 x, w3 shf)
{
    w3 offset = 3;
    return x << shf | x >> offset - shf;
}
w3 rotr3(w3 x, w3 shf)
{
    w3 offset = 3;
    return x >> shf | x << offset - shf;
}
w32 rotl32(w32 x, w32 shf)
{
    w32 offset = 32;
    return x << shf | x >> offset - shf;
}
w32 rotr32(w32 x, w32 shf)
{
    w32 offset = 32;
    return x >> shf | x << offset - shf;
}
w3 Generate_Sensor_Trips(w2 bypass4729,
                         w32 vals4730[3],
                         w32 setpoints4731[3])
{
    w1 app_4100;
    w1 app_4101;
    w1 app_4102;
    w1 app_4103;
    w1 app_4104;
    w1 app_4105;
    w1 app_4106;
    w1 app_4107;
    w1 app_4108;
    w1 app_4111;
    w1 app_4112;
    w1 app_4113;
    w1 app_4114;
    w1 app_4115;
    w1 app_4116;
    w1 app_4117;
    w1 app_4118;
    w1 app_4119;
    w1 app_4122;
    w1 app_4123;
    w1 app_4124;
    w1 app_4125;
    w1 app_4126;
    w1 app_4127;
    w1 app_4128;
    w1 app_4129;
    w1 app_4130;
    w1 ifv_4099;
    w1 ifv_4110;
    w1 ifv_4121;
    w3 return_4097;
    return_4097 = 0;
    app_4108 = (w2) 0 == (w2) 2;
    if (app_4108)
    {
        app_4100 = vals4730[(w2) 0] < setpoints4731[(w2) 0];
        app_4101 = (w1) 0 == (bypass4729 >> (w2) 0 & 1);
        app_4102 = (w1) 0 == (bypass4729 >> (w2) 1 & 1);
        app_4103 = app_4101 & app_4102;
        app_4104 = app_4100 & app_4103;
        ifv_4099 = app_4104;
    }
    else
    {
        app_4105 = setpoints4731[(w2) 0] < vals4730[(w2) 0];
        app_4106 = (w1) 0 == (bypass4729 >> (w2) 0 & 1);
        app_4107 = app_4105 & app_4106;
        ifv_4099 = app_4107;
    }
    app_4119 = (w2) 1 == (w2) 2;
    if (app_4119)
    {
        app_4111 = vals4730[(w2) 1] < setpoints4731[(w2) 1];
        app_4112 = (w1) 0 == (bypass4729 >> (w2) 0 & 1);
        app_4113 = (w1) 0 == (bypass4729 >> (w2) 1 & 1);
        app_4114 = app_4112 & app_4113;
        app_4115 = app_4111 & app_4114;
        ifv_4110 = app_4115;
    }
    else
    {
        app_4116 = setpoints4731[(w2) 1] < vals4730[(w2) 1];
        app_4117 = (w1) 0 == (bypass4729 >> (w2) 1 & 1);
        app_4118 = app_4116 & app_4117;
        ifv_4110 = app_4118;
    }
    app_4130 = (w2) 2 == (w2) 2;
    if (app_4130)
    {
        app_4122 = vals4730[(w2) 2] < setpoints4731[(w2) 2];
        app_4123 = (w1) 0 == (bypass4729 >> (w2) 0 & 1);
        app_4124 = (w1) 0 == (bypass4729 >> (w2) 1 & 1);
        app_4125 = app_4123 & app_4124;
        app_4126 = app_4122 & app_4125;
        ifv_4121 = app_4126;
    }
    else
    {
        app_4127 = setpoints4731[(w2) 2] < vals4730[(w2) 2];
        app_4128 = (w1) 0 == (bypass4729 >> (w2) 2 & 1);
        app_4129 = app_4127 & app_4128;
        ifv_4121 = app_4129;
    }
    if (ifv_4099)
    {
        return_4097 |= (w3) 1 << (w32) 0;
    }
    else
    {
        return_4097 &= ~((w3) 1 << (w32) 0);
    }
    if (ifv_4110)
    {
        return_4097 |= (w3) 1 << (w32) 1;
    }
    else
    {
        return_4097 &= ~((w3) 1 << (w32) 1);
    }
    if (ifv_4121)
    {
        return_4097 |= (w3) 1 << (w32) 2;
    }
    else
    {
        return_4097 &= ~((w3) 1 << (w32) 2);
    }
    return return_4097;
}
