import 'package:app/src/widgets/empty_widget.dart';
import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:go_router/go_router.dart';

import 'package:searchable_listview/searchable_listview.dart';

import 'package:app/src/models/shooting_exercise.dart';
import 'package:app/src/widgets/exercise_header.dart';
import 'package:app/src/widgets/exercise_button.dart';

class ExerciseView extends StatefulWidget {
  const ExerciseView({super.key});

  @override
  ExerciseViewState createState() => ExerciseViewState();
}

class ExerciseViewState extends State<ExerciseView> {
  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        leading: BackButton(
          color: Colors.white,
          onPressed: () =>  {
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
      body: Padding(
        padding: const EdgeInsets.symmetric(vertical: 10, horizontal: 15),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            const Text(
              "Shooting",
              textAlign: TextAlign.left,
              style: TextStyle(
                color: Colors.white,
                fontSize: 40,
                fontWeight: FontWeight.bold
              ),
            ),
            const SizedBox(height: 10),
            const ExerciseHeader(),

            Expanded(
              child: SearchableList<ShootingExercise>.seperated(
                autoFocusOnSearch: false,
                initialList: ShootingExercise.exerciseItems,
                builder: (ShootingExercise item) => ExerciseButton(
                  text: item.exerciseTitle,
                  asset: item.imageAsset,
                  rating: item.rating,
                  toNavigate: item.navigateTo,
                ),
                seperatorBuilder: (context, index) => const SizedBox(height: 5),
                loadingWidget: Column(
                  mainAxisAlignment: MainAxisAlignment.center,
                  children: const [
                    CircularProgressIndicator(),
                    SizedBox(
                      height: 20,
                    ),
                    Text('Loading exercises...')
                  ],
                ),
                inputDecoration: InputDecoration(
                  hintText: "Search Exercise",
                  filled: true,
                  fillColor: Colors.white,
                  focusedBorder: OutlineInputBorder(
                    borderRadius: BorderRadius.circular(10.0),
                  ),
                ),
                style: const TextStyle(
                  color: Colors.black,
                ),
                emptyWidget: const EmptyView(),
                onItemSelected: (ShootingExercise item) {},
                filter: (String query) => ShootingExercise.exerciseItems.where((element) => element.exerciseTitle.toLowerCase().contains(query)).toList()
              )
            )
          ],
        )
      ),
    );
  }
}
