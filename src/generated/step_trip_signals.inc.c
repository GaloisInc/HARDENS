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
w3 Generate_Sensor_Trips(w32 vals4733[3], w32 setpoints4734[3])
{
    w1 app_4100;
    w1 app_4101;
    w1 app_4102;
    w1 app_4105;
    w1 app_4106;
    w1 app_4107;
    w1 app_4110;
    w1 app_4111;
    w1 app_4112;
    w1 ifv_4099;
    w1 ifv_4104;
    w1 ifv_4109;
    w3 return_4097;
    return_4097 = 0;
    app_4102 = (w2) 0 == (w2) 2;
    if (app_4102)
    {
        app_4100 = vals4733[(w2) 0] < setpoints4734[(w2) 0];
        ifv_4099 = app_4100;
    }
    else
    {
        app_4101 = setpoints4734[(w2) 0] < vals4733[(w2) 0];
        ifv_4099 = app_4101;
    }
    app_4107 = (w2) 1 == (w2) 2;
    if (app_4107)
    {
        app_4105 = vals4733[(w2) 1] < setpoints4734[(w2) 1];
        ifv_4104 = app_4105;
    }
    else
    {
        app_4106 = setpoints4734[(w2) 1] < vals4733[(w2) 1];
        ifv_4104 = app_4106;
    }
    app_4112 = (w2) 2 == (w2) 2;
    if (app_4112)
    {
        app_4110 = vals4733[(w2) 2] < setpoints4734[(w2) 2];
        ifv_4109 = app_4110;
    }
    else
    {
        app_4111 = setpoints4734[(w2) 2] < vals4733[(w2) 2];
        ifv_4109 = app_4111;
    }
    if (ifv_4099)
    {
        return_4097 |= (w3) 1 << (w32) 0;
    }
    else
    {
        return_4097 &= ~((w3) 1 << (w32) 0);
    }
    if (ifv_4104)
    {
        return_4097 |= (w3) 1 << (w32) 1;
    }
    else
    {
        return_4097 &= ~((w3) 1 << (w32) 1);
    }
    if (ifv_4109)
    {
        return_4097 |= (w3) 1 << (w32) 2;
    }
    else
    {
        return_4097 &= ~((w3) 1 << (w32) 2);
    }
    return return_4097;
}
w1 Is_Ch_Tripped(w2 mode4726, w1 sensor_tripped4727)
{
    w1 app_4114;
    w1 app_4115;
    w1 app_4116;
    w1 app_4117;
    w1 return_4113;
    return_4113 = 0;
    app_4114 = mode4726 == (w2) 2;
    app_4115 = mode4726 == (w2) 1;
    app_4116 = app_4115 & sensor_tripped4727;
    app_4117 = app_4114 | app_4116;
    return_4113 = app_4117;
    return return_4113;
}
