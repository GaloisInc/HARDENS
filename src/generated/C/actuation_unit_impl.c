typedef unsigned _ExtInt(1) w1;
typedef unsigned _ExtInt(2) w2;
typedef unsigned _ExtInt(8) w8;
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
w1 Actuate_D0(w8 trips4819[3][4], w1 old4820)
{
    w1 app_4127;
    w1 app_4128;
    w1 app_4129;
    w1 app_4130;
    w1 return_4115;
    return_4115 = 0;
    app_4127 = Coincidence_2_4(trips4819[(w2) 0]);
    app_4128 = Coincidence_2_4(trips4819[(w2) 1]);
    app_4129 = app_4127 | app_4128;
    app_4130 = app_4129 | old4820;
    return_4115 = app_4130;
    return return_4115;
}
w1 Actuate_D1(w8 trips4824[3][4], w1 old4825)
{
    w1 app_4135;
    w1 app_4136;
    w1 return_4132;
    return_4132 = 0;
    app_4135 = Coincidence_2_4(trips4824[(w2) 2]);
    app_4136 = app_4135 | old4825;
    return_4132 = app_4136;
    return return_4132;
}
w1 Coincidence_2_4(w8 x4847[4])
{
    w1 app_4098;
    w1 app_4099;
    w1 app_4100;
    w1 app_4101;
    w1 app_4102;
    w1 app_4103;
    w1 app_4104;
    w1 app_4105;
    w1 app_4106;
    w1 app_4107;
    w1 app_4108;
    w1 app_4109;
    w1 app_4110;
    w1 app_4111;
    w1 app_4112;
    w1 return_4097;
    return_4097 = 0;
    app_4098 = x4847[(w2) 0] != (w8) 0;
    app_4099 = x4847[(w2) 1] != (w8) 0;
    app_4100 = app_4098 & app_4099;
    app_4101 = x4847[(w2) 0] != (w8) 0;
    app_4102 = x4847[(w2) 1] != (w8) 0;
    app_4103 = app_4101 | app_4102;
    app_4104 = x4847[(w2) 2] != (w8) 0;
    app_4105 = x4847[(w2) 3] != (w8) 0;
    app_4106 = app_4104 | app_4105;
    app_4107 = app_4103 & app_4106;
    app_4108 = x4847[(w2) 2] != (w8) 0;
    app_4109 = x4847[(w2) 3] != (w8) 0;
    app_4110 = app_4108 & app_4109;
    app_4111 = app_4107 | app_4110;
    app_4112 = app_4100 | app_4111;
    return_4097 = app_4112;
    return return_4097;
}
