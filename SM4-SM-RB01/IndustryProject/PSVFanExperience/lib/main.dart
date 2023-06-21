import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:provider/provider.dart';

import 'package:psv_fan_experience/src/providers/submission_provider.dart';
import 'package:psv_fan_experience/src/router.dart';
import 'package:psv_fan_experience/src/theme.dart';

void main() {
  WidgetsFlutterBinding.ensureInitialized();
  SystemChrome.setPreferredOrientations(
      [DeviceOrientation.portraitUp, DeviceOrientation.portraitDown]);
  runApp(
    MultiProvider(
      providers: [
        ChangeNotifierProvider(create: (_) => SubmissionProvider())
      ],
      child: const MyApp()
    )
  );
}

class MyApp extends StatelessWidget {
  const MyApp({super.key});

  @override
  Widget build(BuildContext context) {
    return MaterialApp.router(
      title: 'PSV Fan Experience',
      debugShowCheckedModeBanner: false,
      theme: AppTheme.defaultTheme,
      routerConfig: router,
    );
  }
}
