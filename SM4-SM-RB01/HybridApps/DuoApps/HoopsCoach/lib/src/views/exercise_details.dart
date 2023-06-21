import 'package:app/src/widgets/badge_section.dart';
import 'package:flutter/material.dart';

import 'package:app/src/widgets/instructions_section.dart';
import 'package:app/src/models/shooting_exercise.dart';
import 'package:app/src/widgets/image_header.dart';
import 'package:app/src/widgets/video_section.dart';
import 'package:flutter/services.dart';

import 'package:go_router/go_router.dart';

class ExerciseDetails extends StatefulWidget {
  const ExerciseDetails({super.key});

  @override
  ExerciseDetailsState createState() => ExerciseDetailsState();
}

class ExerciseDetailsState extends State<ExerciseDetails> {
  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        leading: BackButton(
          color: Colors.white,
          onPressed: () => {
            HapticFeedback.lightImpact(),
            GoRouter.of(context).pop(),
          }
        ),
        title: const Text(
            "",
            style: TextStyle(
              color: Colors.black,
              fontWeight: FontWeight.bold,
              fontSize: 40,
            )
        ),
        backgroundColor: Colors.transparent,
      ),
      body: SingleChildScrollView(
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            ImageHeader(
              exercise: ShootingExercise.exerciseItems[0],
              description: 'Test your shooting from behind the free-throw line',
              asset: 'stephen_curry'
            ),
            const VideoSection(title: "Video Guide", asset: 'fundamentals_shooting'),
            const InstructionSection(),
            const BadgeSection(),
          ],
        ),
      ),
    );
  }
}
