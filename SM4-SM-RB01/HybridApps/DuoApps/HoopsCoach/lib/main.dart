import 'package:app/src/providers/achievements_provider.dart';
import 'package:flutter/material.dart';
import 'package:flutter/services.dart';

import 'package:app/src/theme.dart';
import 'package:app/src/router.dart';
import 'package:provider/provider.dart';

void main() {
  WidgetsFlutterBinding.ensureInitialized();
  SystemChrome.setPreferredOrientations(
      [DeviceOrientation.portraitUp, DeviceOrientation.portraitDown]);
  runApp(
    MultiProvider(
      providers: [ChangeNotifierProvider(create: (_) => AchievementProvider())],
      child: const MyApp(),
    )
  );
}

class MyApp extends StatelessWidget {
  const MyApp({super.key});

  @override
  Widget build(BuildContext context) {
    return MaterialApp.router(
      title: 'Hoops Coach',
      debugShowCheckedModeBanner: false,
      theme: AppTheme.defaultTheme,
      routerConfig: router,
    );
  }
}
