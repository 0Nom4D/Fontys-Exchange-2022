import 'package:flutter/material.dart';

const Color successColor = Color(0xFF00B74A);

const Color backgroundColor = Colors.black;

const Color dangerColor = Color(0xFFF93154);

const Color warningColor = Color(0xFFFFA900);

const Color infoColor = Color(0xFF39C0ED);

const ColorScheme appScheme = ColorScheme(
    primary: Colors.white,
    secondary: Colors.black,
    tertiary: backgroundColor,
    background: backgroundColor,
    brightness: Brightness.light,
    onError: dangerColor,
    error: dangerColor,
    onPrimary: Colors.black,
    onSecondary: Colors.white,
    onTertiary: Colors.white,
    onBackground: Colors.white,
    surface: Colors.white,
    onSurface: Colors.black
);

class AppTheme {
  static final ThemeData defaultTheme = ThemeData.from(colorScheme: appScheme);
}
