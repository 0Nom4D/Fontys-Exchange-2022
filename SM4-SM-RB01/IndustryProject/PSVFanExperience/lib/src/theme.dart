import 'package:flutter/material.dart';

const Color psvRed = Color(0xFFED1C24);

const Color psvBlack = Color(0xFF000000);

const Color psvWhite = Color(0xFFFFFFFF);

const Color psvGrey = Color(0xFFCCCCCC);

const Color successColor = Color(0xFF00B74A);

const Color dangerColor = Color(0xFFF93154);

const ColorScheme appScheme = ColorScheme(
    primary: psvRed,
    secondary: psvBlack,
    tertiary: psvGrey,
    background: psvWhite,
    brightness: Brightness.light,
    onError: dangerColor,
    error: dangerColor,
    onPrimary: psvWhite,
    onSecondary: psvWhite,
    onTertiary: psvBlack,
    onBackground: psvBlack,
    surface: psvWhite,
    onSurface: psvBlack
);

class AppTheme {
  static final ThemeData defaultTheme = ThemeData(
    fontFamily: 'Klavika',
    colorScheme: appScheme
  );
}
