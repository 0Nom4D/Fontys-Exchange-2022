import 'package:flutter/material.dart';

import 'package:camera_techcase/src/router.dart';
import 'package:camera_techcase/src/theme.dart';

void main() {
  runApp(const MyApp());
}

class MyApp extends StatelessWidget {
  const MyApp({super.key});

  @override
  Widget build(BuildContext context) {
    return MaterialApp.router(
      debugShowCheckedModeBanner: false,
      theme: AppTheme.defaultTheme,
      routerConfig: router,
    );
  }
}